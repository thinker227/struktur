//! Type checking and inference.
//!
//! The algorithm used for type inference is [Algorithm-J](https://en.wikipedia.org/wiki/Hindley-Milner_type_system#Algorithm_J),
//! with the implementation heavily referencing [brendanzab's Language Garden project](https://github.com/brendanzab/language-garden/blob/main/scraps/check_poly_algorithm_j.ml)
//! and [an example by jfetcher](https://github.com/jfecher/algorithm-j).
//! Most notably, Algorithm-J uses mutable unification variables instead of a substitution map,
//! so [MetaVar] is implemented using interior mutability.

mod var;

use std::{cell::RefCell, collections::{HashMap, hash_map::Entry}};

use derivative::Derivative;
use petgraph::{algo::tarjan_scc, graph::{DiGraph, NodeIndex as GraphNode}};
use crate::{ast::*, id::IdProvider, stage::{Sem, Typed}, symbols::{Symbol, SymbolData}, types::{Forall, FunctionType, MonoType, PolyType, Primitive, Pruned, Repr, TypeVar, TypedExprData, TypedFunctionData, TypedVariableData}};
use self::var::MetaVar;

/*----------------------*\
|  Type representations  |
\*----------------------*/

/// Types that may have unification variables.
struct Vars;

impl Repr for Vars {
    type RecTy = InferType;
}

/// A type which might be a unification variable.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""), PartialEq(bound = ""))]
enum InferType {
    /// A normal type.
    Type(MonoType<Vars>),
    /// A unification type variable.
    Var(MetaVar),
}

impl From<MonoType<Vars>> for InferType {
    fn from(value: MonoType<Vars>) -> Self {
        Self::Type(value)
    }
}

impl From<MetaVar> for InferType {
    fn from(value: MetaVar) -> Self {
        Self::Var(value)
    }
}

impl From<Primitive> for InferType {
    fn from(value: Primitive) -> Self {
        Self::Type(MonoType::Primitive(value))
    }
}

impl From<FunctionType<Vars>> for InferType {
    fn from(value: FunctionType<Vars>) -> Self {
        Self::Type(value.into())
    }
}

impl From<TypeVar> for InferType {
    fn from(value: TypeVar) -> Self {
        Self::Type(MonoType::Var(value))
    }
}

/*-------------------*\
|  Inference context  |
\*-------------------*/

#[derive(Debug)]
struct RawContext {
    // Only bindings can be forall generalizations, expressions themselves cannot.
    expr_types: RefCell<HashMap<NodeId, InferType>>,
    symbol_types: RefCell<HashMap<Symbol, PolyType<InferType>>>,
    id_provider: IdProvider,
}

impl RawContext {
    pub fn new() -> Self {
        Self {
            expr_types: RefCell::new(HashMap::new()),
            symbol_types: RefCell::new(HashMap::new()),
            id_provider: IdProvider::new_plain()
        }
    }

    pub fn into_types(self) -> (HashMap<NodeId, InferType>, HashMap<Symbol, PolyType<InferType>>) {
        (self.expr_types.into_inner(), self.symbol_types.into_inner())
    }
}

/// Context for type-checking and inference.
#[derive(Debug, Clone, Copy)]
struct Context<'raw> {
    forall_level: usize,
    raw: &'raw RawContext,
}

impl<'raw> Context<'raw> {
    /// Creates a new context.
    pub fn new(raw: &'raw RawContext) -> Self {
        Self {
            forall_level: 0,
            raw
        }
    }

    /// Creates a fresh meta-variable with the context's current level.
    #[must_use]
    pub fn fresh_meta(&self) -> MetaVar {
        MetaVar::new(
            self.raw.id_provider.next(),
            self.forall_level
        )
    }

    /// "Extends" the context by returning a new one with the level incremented by 1.
    #[must_use]
    pub fn extend(&self) -> Self {
        Self {
            forall_level: self.forall_level + 1,
            raw: self.raw
        }
    }

    /// Adds an expression-to-type mapping.
    pub fn add_expr_ty(&self, key: NodeId, ty: InferType) -> Result<(), InferType> {
        let mut borrow = self.raw.expr_types.borrow_mut();
        match borrow.entry(key) {
            Entry::Occupied(_) => Err(ty),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Adds a symbol-to-type mapping.
    pub fn add_symbol_ty(&self, key: Symbol, ty: PolyType<InferType>) -> Result<(), PolyType<InferType>> {
        let mut borrow = self.raw.symbol_types.borrow_mut();
        match borrow.entry(key) {
            Entry::Occupied(_) => Err(ty),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    pub fn replace_symbol_ty(&self, key: Symbol, ty: PolyType<InferType>) {
        let mut borrow = self.raw.symbol_types.borrow_mut();
        borrow.insert(key, ty);
    }

    /// Tries to get the type for an expression.
    pub fn _lookup_expr(&self, key: NodeId) -> Option<InferType> {
        self.raw.expr_types.borrow().get(&key).cloned()
    }

    /// Tries to get the type for a symbol.
    pub fn lookup_symbol(&self, key: Symbol) -> Option<PolyType<InferType>> {
        self.raw.symbol_types.borrow().get(&key).cloned()
    }
}

/*---------------------------------*\
|  Type substitution/instantiation  |
\*---------------------------------*/

impl InferType {
    /// Substitutes type variables within the type for other types.
    pub fn substitute(&self, subs: &HashMap<TypeVar, InferType>) -> Self {
        match self {
            Self::Type(ty) => ty.substitute(subs),
            Self::Var(var) => var.get_sub().cloned()
                .unwrap_or_else(|| var.clone().into())
        }
    }
}

impl MonoType<Vars> {
    /// Substitutes type variables within the type for other types.
    pub fn substitute(&self, subs: &HashMap<TypeVar, InferType>) -> InferType {
        match self {
            Self::Primitive(primitive) => (*primitive).into(),
            Self::Function(func) => func.substitute(subs).into(),
            Self::Var(var) => subs.get(var).cloned()
                .unwrap_or_else(|| (*var).into()),
        }
    }
}

impl FunctionType<Vars> {
    /// Substitutes type variables within the type for other types.
    pub fn substitute(&self, subs: &HashMap<TypeVar, InferType>) -> Self {
        let param = self.param.substitute(subs);
        let ret = self.param.substitute(subs);
        Self { param, ret }
    }
}

impl Forall<InferType> {
    /// Instantiates the generalization, turning all type parameters into fresh meta variables.
    pub fn instantiate(&self, ctx: &Context) -> InferType {
        let subs = self.vars.iter()
            .map(|var| (*var, InferType::Var(ctx.fresh_meta())))
            .collect();

        self.target.substitute(&subs)
    }
}

/*------------*\
|  Algorithms  |
\*------------*/

/// Checks whether a unification variable occurs within another type.
fn occurs(var: &MetaVar, within: &InferType) -> bool {
    match within {
        InferType::Type(MonoType::Function(function)) =>
            occurs(var, &function.param) || occurs(var, &function.ret),

        InferType::Var(other) => match other.get_sub() {
            Some(sub) => occurs(other, sub),
            None => other == var
        }

        _ => false
    }
}

/// Attempts to lower the level of any unification variables within a type to a given level.
fn lower(ty: &InferType, level: usize) {
    match ty {
        InferType::Type(MonoType::Function(function)) => {
            lower(&function.param, level);
            lower(&function.ret, level);
        }

        InferType::Var(var) => match var.get_sub() {
            Some(x) => lower(x, level),
            None => {
                _ = var.try_lower_level(level);
            }
        }

        _ => {}
    }
}

/// Attempts to unify two types.
fn unify(a: &InferType, b: &InferType, level: usize) {
    match (a, b) {
        // Unifying a meta variable with itself does nothing.
        (
            InferType::Var(a),
            InferType::Var(b)
        ) if a == b => {}

        // Unifying a type variable with itself does nothing.
        (
            InferType::Type(MonoType::Var(a)),
            InferType::Type(MonoType::Var(b))
        ) if a == b => {}

        (
            InferType::Type(MonoType::Primitive(a)),
            InferType::Type(MonoType::Primitive(b))
        ) if a == b => {}

        (
            InferType::Type(MonoType::Function(a)),
            InferType::Type(MonoType::Function(b))
        ) => {
            unify(&a.param, &b.param, level);
            unify(&a.ret, &b.ret, level);
        }

        // Unify through solved meta variables.
        (InferType::Var(var), ty) if let Some(sub) = var.get_sub() =>
            unify(sub, ty, level),
        (ty, InferType::Var(var)) if let Some(sub) = var.get_sub() =>
            unify(ty, sub, level),

        (InferType::Var(var), ty) |
        (ty, InferType::Var(var)) =>
        match var.get_sub() {
            // Already checked for solved meta variables above.
            Some(_) => unreachable!(),
            None => {
                if occurs(var, ty) {
                    panic!("{var:?} occurs within {ty:?}");
                }

                lower(ty, level);

                if var.sub(ty.clone()).is_err() {
                    panic!("{var:?} has already been substituted");
                }
            }
        }

        _ => panic!("cannot unify {a:?} and {b:?}")
    }
}

/// Replaces any unsolved unification variables with type variables within a forall generalization.
///
/// Returns [`Err`] if the type does not contain any unsolved unification variables.
fn generalize(ctx: &Context, ty: InferType) -> Result<Forall<InferType>, InferType> {
    fn visit(ctx: &Context, vars: &mut Vec<TypeVar>, ty: &InferType) {
        static PROVIDER: IdProvider<TypeVar> = IdProvider::new(TypeVar);

        match ty {
            InferType::Type(MonoType::Function(function)) => {
                visit(ctx, vars, &function.param);
                visit(ctx, vars, &function.ret);
            }

            InferType::Var(meta_var) => match meta_var.get_sub() {
                Some(x) => visit(ctx, vars, x),

                // Ensure that we're not generalizing meta variables introducted in a more nested binding.
                None if ctx.forall_level < meta_var.level() => {
                    let type_var = PROVIDER.next();
                    meta_var.sub(type_var.into()).unwrap();
                    vars.push(type_var);
                }

                None => {}
            }

            _ => {}
        }
    }

    let mut vars = Vec::new();
    visit(ctx, &mut vars, &ty);

    if vars.is_empty() {
        Err(ty)
    } else {
        Ok(Forall {
            vars,
            target: ty
        })
    }
}

/// Infers the type of an expression and adds it to the context.
fn infer(ctx: &Context, Expr(expr, _, node_data): &Expr<Sem>) -> InferType {
    let ty: InferType = match expr {
        // Primitives are just their respective types.
        ExprVal::Unit => InferType::Type(MonoType::Primitive(Primitive::Unit)),
        ExprVal::Int(_) => InferType::Type(MonoType::Primitive(Primitive::Int)),
        ExprVal::Bool(_) => InferType::Type(MonoType::Primitive(Primitive::Bool)),
        ExprVal::String(_) => InferType::Type(MonoType::Primitive(Primitive::String)),

        ExprVal::Var(var) => match ctx.lookup_symbol(*var) {
            // A Variable may be a forall generalization, so instantiate it if it is one,
            // otherwise just use the non-generalized type.
            Some(PolyType::Forall(f)) => f.instantiate(ctx),
            Some(PolyType::Type(t)) => t,
            None => panic!("no type for variable {var:?}")
        }

        ExprVal::Bind(binding) => {
            // Infer the type of the value assigned to the binding using a forall level one higher than before.
            // This ensures that unsolved meta variables within the binding properly become type variables
            // in a forall generalization.
            let val_ty = infer(&ctx.extend(), &binding.value);

            // Try to generalize the type. Since let-bindings cannot have forward-declarations,
            // it is guaranteed that all meta variables within the binding are in their final solved/unsolved
            // state after the binding's type has been inferred.
            let general = match generalize(ctx, val_ty) {
                Ok(forall) => PolyType::Forall(forall),
                Err(ty) => PolyType::Type(ty)
            };
            ctx.add_symbol_ty(binding.symbol, general).unwrap();

            // Now that we have the type of the binding in the context, we can infer the return expression.
            infer(ctx, &binding.expr)
        }

        ExprVal::Lambda(lambda) => {
            // Relatively simple, just assign the parameter a fresh meta variable and then infer the body.

            let param_ty = InferType::Var(ctx.fresh_meta());
            ctx.add_symbol_ty(lambda.param, PolyType::Type(param_ty.clone())).unwrap();

            let ret_ty = infer(ctx, &lambda.body);

            InferType::Type(MonoType::function(param_ty, ret_ty))
        }

        ExprVal::Apply(app) => {
            let target_ty = infer(ctx, &app.target);
            let arg_ty = infer(ctx, &app.arg);
            let ret_ty = InferType::Var(ctx.fresh_meta());

            // The target of an application should always be a function,
            // so unify the target with a function from the argument type to the return type.
            unify(
                &target_ty,
                &InferType::Type(MonoType::function(
                    arg_ty,
                    ret_ty.clone()
                )),
                ctx.forall_level
            );

            ret_ty
        }
    };

    ctx.add_expr_ty(node_data.id, ty.clone()).unwrap();

    ty
}

/// Prunes away all the unification variables from a type.
fn prune(ty: &InferType) -> MonoType<Pruned> {
    match ty {
        InferType::Type(MonoType::Primitive(primitive)) => MonoType::Primitive(*primitive),
        InferType::Type(MonoType::Function(function)) => MonoType::function(
            prune(&function.param),
            prune(&function.ret)
        ),
        InferType::Type(MonoType::Var(var)) => MonoType::Var(*var),
        InferType::Var(var) => match var.get_sub() {
            Some(ty) => prune(ty),
            None => panic!("unsubstituted type variable {ty:?}")
        },
    }
}

/*-------------------*\
|  Reference tracing  |
\*-------------------*/

/// Traces the reference graph of a binding.
struct Referencer<'a> {
    current: GraphNode,
    functions: &'a HashMap<Symbol, GraphNode>,
    graph: &'a mut DiGraph<Symbol, ()>,
}

impl Visitor for Referencer<'_> {
    type S = Sem;

    fn var_expr(&mut self, symbol: &Symbol, _: ExprDataBundle<'_, Self::S>) {
        if let Some(referenced) = self.functions.get(symbol) {
            self.graph.add_edge(self.current, *referenced, ());
        }
    }
}

/// Constructs a graph of references between top-level bindings.
fn reference_graph(ast: &Ast<Sem>) -> DiGraph<Symbol, ()> {
    let mut graph = DiGraph::new();

    let items = &ast.root().0;

    let mut functions = HashMap::new();
    for Item(item, _) in items {
        match item {
            ItemVal::Binding(function) => {
                let index = graph.add_node(function.symbol);
                functions.insert(function.symbol, index);
            }
        }
    }

    for Item(item, data) in items {
        match item {
            ItemVal::Binding(function) => {
                let mut referencer = Referencer {
                    current: *functions.get(&function.symbol).unwrap(),
                    functions: &functions,
                    graph: &mut graph
                };
                referencer.function(function, data);
            }
        }
    }

    graph
}

/*-----------*\
|  Embedding  |
\*-----------*/

/// Embeds types into an AST.
struct Embedder {
    expr_types: HashMap<NodeId, InferType>,
    symbol_types: HashMap<Symbol, PolyType<InferType>>,
}

impl Embedder {
    fn get_expr_type(&self, expr: NodeId) -> MonoType<Pruned> {
        match self.expr_types.get(&expr) {
            Some(ty) => prune(ty),
            None => panic!("node {expr:?} does not have a type")
        }
    }

    fn get_symbol_type(&self, symbol: Symbol) -> PolyType<MonoType<Pruned>> {
        match self.symbol_types.get(&symbol) {
            Some(ty) => ty.clone().map(|ty| prune(&ty)),
            None => panic!("symbol {symbol:?} does not have a type")
        }
    }

    fn get_function_type(&self, symbol: Symbol) -> PolyType<FunctionType<Pruned>> {
        self.get_symbol_type(symbol).map(|ty| match ty {
            MonoType::Function(function) => function.as_ref().clone(),
            _ => panic!("expected function type")
        })
    }

    pub fn ast(&self, ast: &Ast<Sem>) -> Ast<Typed> {
        let typed_root = self.root(ast.root());

        let typed_symbols = ast.symbols()
            .map(|symbol, data| self.symbol(symbol, data));

        Ast::new(typed_root, typed_symbols, ())
    }

    fn symbol(&self, symbol: Symbol, data: &SymbolData<Sem>) -> SymbolData<Typed> {
        match data {
            SymbolData::Var(var) => SymbolData::Var(var.map::<Typed>(|()|
                TypedVariableData {
                    ty: self.get_symbol_type(symbol)
                }
            )),
            SymbolData::Func(function) => SymbolData::Func(function.map::<Typed>(|()|
                TypedFunctionData {
                    ty: self.get_function_type(symbol)
                }
            ))
        }
    }

    fn root(&self, Root(items, node_data): &Root<Sem>) -> Root<Typed> {
        let typed_items = items.iter()
            .map(|item| self.item(item))
            .collect();

        Root(typed_items, node_data.clone().map(|span| span))
    }

    fn item(&self, Item(item, node_data): &Item<Sem>) -> Item<Typed> {
        let typed_item = match item {
            ItemVal::Binding(function) => {
                let typed_body = self.expr(&function.body);
                ItemVal::Binding(Binding {
                    body: typed_body,
                    symbol: function.symbol,
                    param: function.symbol
                })
            }
        };

        Item(typed_item, node_data.clone().map(|span| span))
    }

    fn expr(&self, Expr(expr, _, node_data): &Expr<Sem>) -> Expr<Typed> {
        let typed_expr = match expr {
            ExprVal::Unit => ExprVal::Unit,
            ExprVal::Int(x) => ExprVal::Int(*x),
            ExprVal::Bool(x) => ExprVal::Bool(*x),
            ExprVal::String(x) => ExprVal::String(x.clone()),
            ExprVal::Var(s) => ExprVal::Var(*s),

            ExprVal::Bind(binding) => ExprVal::bind(Let {
                symbol: binding.symbol,
                value: self.expr(&binding.expr),
                expr: self.expr(&binding.expr)
            }),

            ExprVal::Lambda(lambda) => ExprVal::lambda(Lambda {
                param: lambda.param,
                body: self.expr(&lambda.body)
            }),

            ExprVal::Apply(application) => ExprVal::apply(Application {
                target: self.expr(&application.target),
                arg: self.expr(&application.arg)
            })
        };

        let ty = self.get_expr_type(node_data.id);

        Expr(
            typed_expr,
            TypedExprData { ty },
            node_data.clone().map(|span| span)
        )
    }
}

/*--------------------*\
|  Core type-checking  |
\*--------------------*/

/// Performs type checking and type inference on all the expressions and bindings of an AST.
pub fn type_check(ast: &Ast<Sem>) -> Ast<Typed> {
    // Fetch the reference graph for the tree and compute the strongly-connected components.
    // This is used to know what groups of top-levels bindings need to be inferred together
    // so that unification variables won't unnecessarily leak from one function into another.
    let references = reference_graph(ast);
    let scc = tarjan_scc(&references);
    let groups = scc.iter()
        .map(|group| group.iter()
            .map(|index| *references.node_weight(*index).unwrap())
            .collect::<Vec<_>>()
        );

    let raw_ctx = RawContext::new();
    let ctx = Context::new(&raw_ctx);

    let mut function_types = HashMap::new();

    for group in groups {
        // Create types for each function and their parameters
        // so that every function in the group has a corresponding type when inferring their bodies.
        for item in &group {
            let decl = ast.symbols().get(*item).decl();
            let ItemVal::Binding(function) = &ast.get_node_as::<Item<Sem>>(decl).unwrap().0;

            // Make sure that the fresh meta variables do not have level 0.
            let ctx = ctx.extend();

            let param_var = ctx.fresh_meta();
            let ret_var = ctx.fresh_meta();
            let function_ty = FunctionType {
                param: InferType::Var(param_var.clone()),
                ret: InferType::Var(ret_var)
            };

            function_types.insert(*item, function_ty.clone());

            ctx.add_symbol_ty(function.param, PolyType::Type(param_var.into())).unwrap();
            ctx.add_symbol_ty(*item, PolyType::Type(function_ty.into())).unwrap();
        }

        // Infer the bodies of each function.
        for item in &group {
            let decl = ast.symbols().get(*item).decl();
            let ItemVal::Binding(function) = &ast.get_node_as::<Item<Sem>>(decl).unwrap().0;

            let ctx = ctx.extend();

            let ret_ty = infer(&ctx, &function.body);

            let function_ty = function_types.get(item).unwrap();

            // Important that the level here is 1,
            // since unification variables declared at the top-level
            // would otherwise not be able to have their levels lowerd properly.
            unify(&ret_ty, &function_ty.ret, 1);
        }

        // Try to generalize the function types.
        for item in &group {
            let function_ty = function_types.get(item).unwrap();

            // If we can generalize the function type then replace the type in the context for further use.
            // Otherwise, the type can just be used as-is since it doesn't contain any unsolved unification variables.
            if let Ok(general) = generalize(&ctx, function_ty.clone().into()) {
                ctx.replace_symbol_ty(*item, PolyType::Forall(general));
            }
        }
    }

    // Prune the fully type-checked AST of any unification variables and embed the types into each node.
    let (expr_types, symbol_types) = raw_ctx.into_types();
    let embedder = Embedder {
        expr_types,
        symbol_types
    };
    embedder.ast(ast)
}

#[cfg(test)]
mod tests {
    // use crate::{stage::Parse, symbols, types::pretty_print::pretty_print};
    // use super::*;

    // #[test]
    // fn r#const() {
    //     let id: Item<Parse> = Item(
    //         ItemVal::Function(Function {
    //             symbol: String::from("const"),
    //             param: String::from("x"),
    //             body: Expr(
    //                 // ExprVal::apply(Application {
    //                 //     target: Expr(
    //                 //         ExprVal::Var(String::from("id")),
    //                 //         (),
    //                 //         NodeData {
    //                 //             data: (),
    //                 //             id: NodeId::next()
    //                 //         }
    //                 //     ),
    //                 //     arg: Expr(
    //                 //         ExprVal::Unit,
    //                 //         (),
    //                 //         NodeData {
    //                 //             data: (),
    //                 //             id: NodeId::next()
    //                 //         }
    //                 //     )
    //                 // }),
    //                 ExprVal::apply(Application {
    //                     target: Expr(
    //                         ExprVal::Var(String::from("x")),
    //                         (),
    //                         NodeData {
    //                             data: (),
    //                             id: NodeId::next()
    //                         }
    //                     ),
    //                     arg: Expr(
    //                         ExprVal::String(String::from("uwu")),
    //                         (),
    //                         NodeData {
    //                             data: (),
    //                             id: NodeId::next()
    //                         }
    //                     )
    //                 }),
    //                 // ExprVal::lambda(Lambda {
    //                 //     param: String::from("y"),
    //                 //     body: Expr(
    //                 //         ExprVal::Var(String::from("x")),
    //                 //         (),
    //                 //         NodeData {
    //                 //             data: (),
    //                 //             id: NodeId::next()
    //                 //         }
    //                 //     )
    //                 // }),
    //                 // ExprVal::Int(0),
    //                 // ExprVal::Var(String::from("x")),
    //                 (),
    //                 NodeData {
    //                     data: (),
    //                     id: NodeId::next()
    //                 }
    //             )
    //         }),
    //         NodeData {
    //             data: (),
    //             id: NodeId::next()
    //         }
    //     );

    //     let root = Root(
    //         vec![id],
    //         NodeData {
    //             data: (),
    //             id: NodeId::next()
    //         }
    //     );

    //     let parse = Ast::new(root, (), ());
    //     let sem = symbols::resolve_symbols(&parse);
    //     let typed = type_check(&sem);

    //     for item in &typed.root().0 {
    //         match &item.0 {
    //             ItemVal::Function(function) => {
    //                 let function = match typed.symbols().get(function.symbol) {
    //                     SymbolData::Func(f) => f,
    //                     SymbolData::Var(_) => unreachable!()
    //                 };

    //                 println!("\n{} :: {}\n", &function.name, pretty_print(&function.data.ty));
    //             }
    //         }
    //     }
    // }
}
