#![allow(unused_assignments)]

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
use crate::{ast::{visit::{VisitT, Visitor}, *}, id::IdProvider, patterns::{Cases, compile_pattern}, stage::{Sem, Typed}, symbols::{Symbol, SymbolKind}, text_span::TextSpan, types::{Forall, FunctionType, MonoType, PolyType, Primitive, Pruned, Repr, TypeVar, TypedBindingData, TypedExprData, TypedVariableData, pretty_print::{PrettyPrint, PrintCtx, pretty_print_with}}, visit};

pub use self::var::MetaVar;

/*--------*\
|  Errors  |
\*--------*/

/// An error produced by type checking.
#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum TypeCheckError {
    #[error("Cannot unify types `{a}` and `{b}`")]
    IncompatibleTypes {
        #[label]
        span: TextSpan,
        a: String,
        b: String,
    },

    #[error("Cannot construct infinite type from constraint `{var}` = `{ty}`")]
    OccursCheck {
        #[label]
        span: TextSpan,
        var: String,
        ty: String,
    },
}

type InferResult<T> = Result<T, TypeCheckError>;

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

impl PrettyPrint for InferType {
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            InferType::Type(ty) => ty.pretty_print(buf, ctx),
            InferType::Var(var) => var.pretty_print(buf, ctx)
        }
    }
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
            Self::Var(var) => match var.get_sub() {
                Some(ty) => ty.substitute(subs),
                None => var.clone().into()
            }
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
        let ret = self.ret.substitute(subs);
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
            Some(sub) => occurs(var, sub),
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
fn unify(a: &InferType, b: &InferType, level: usize, source: TextSpan) -> InferResult<()> {
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
            unify(&a.param, &b.param, level, source)?;
            unify(&a.ret, &b.ret, level, source)?;
        }

        // Unify through solved meta variables.
        (InferType::Var(var), ty) if let Some(sub) = var.get_sub() =>
            unify(sub, ty, level, source)?,
        (ty, InferType::Var(var)) if let Some(sub) = var.get_sub() =>
            unify(ty, sub, level, source)?,

        (InferType::Var(var), ty) |
        (ty, InferType::Var(var)) =>
        match var.get_sub() {
            // Already checked for solved meta variables above.
            Some(_) => unreachable!(),
            None => {
                if occurs(var, ty) {
                    let mut ctx = PrintCtx::new();
                    return Err(TypeCheckError::OccursCheck {
                        span: source,
                        var: pretty_print_with(var, &mut ctx),
                        ty: pretty_print_with(ty, &mut ctx)
                    });
                }

                lower(ty, level);

                if var.sub(ty.clone()).is_err() {
                    panic!("{var:?} has already been substituted");
                }
            }
        }

        _ => {
            let mut ctx = PrintCtx::new();
            return Err(TypeCheckError::IncompatibleTypes {
                span: source,
                a: pretty_print_with(a, &mut ctx),
                b: pretty_print_with(b, &mut ctx)
            })
        }
    }

    Ok(())
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
fn infer(ctx: &Context, expr: &Expr<Sem>) -> InferResult<InferType> {
    let ty: InferType = match expr {
        // Primitives are just their respective types.
        Expr::Unit(_) => InferType::Type(MonoType::Primitive(Primitive::Unit)),
        Expr::Int(_) => InferType::Type(MonoType::Primitive(Primitive::Int)),
        Expr::Bool(_) => InferType::Type(MonoType::Primitive(Primitive::Bool)),
        Expr::String(_) => InferType::Type(MonoType::Primitive(Primitive::String)),

        Expr::Var(var) => match ctx.lookup_symbol(var.symbol) {
            // A Variable may be a forall generalization, so instantiate it if it is one,
            // otherwise just use the non-generalized type.
            Some(PolyType::Forall(f)) => f.instantiate(ctx),
            Some(PolyType::Type(t)) => t,
            None => panic!("no type for variable {var:?}")
        }

        Expr::Bind(binding) => {
            // Infer the type of the value assigned to the binding using a forall level one higher than before.
            // This ensures that unsolved meta variables within the binding properly become type variables
            // in a forall generalization.
            let val_ty = infer(&ctx.extend(), &binding.value)?;

            // Try to generalize the type. Since let-bindings cannot have forward-declarations,
            // it is guaranteed that all meta variables within the binding are in their final solved/unsolved
            // state after the binding's type has been inferred.
            match generalize(ctx, val_ty) {
                Ok(forall) => match &binding.pattern {
                    // Wildcard patterns just discard the value.
                    Pattern::Wildcard(_) => {}

                    // In case the pattern is a variable, give it the generalized type.
                    Pattern::Var(pattern_var) => {
                        ctx.add_symbol_ty(pattern_var.symbol, PolyType::Forall(forall)).unwrap();
                    }

                    // For any other patterns, instantiate the type we just generalized and unify it with the pattern type.
                    _ => {
                        let val_ty = forall.instantiate(ctx);
                        let pattern_ty = pattern(ctx, &binding.pattern)?;
                        unify(&val_ty, &pattern_ty, ctx.forall_level, binding.pattern.span())?;
                    }
                }

                // In case we did not generalize the type, just unify it with the pattern type.
                Err(val_ty) => {
                    let pattern_ty = pattern(ctx, &binding.pattern)?;
                    unify(&val_ty, &pattern_ty, ctx.forall_level, binding.pattern.span())?;
                }
            };

            // Now that we have the type of the binding in the context, we can infer the return expression.
            infer(ctx, &binding.expr)?
        }

        Expr::Lambda(lambda) => {
            // Relatively simple, just assign the parameter a fresh meta variable and then infer the body.

            // Iterate through the lambda cases and successively build up the parameter and return types.
            let param_ty = InferType::Var(ctx.fresh_meta());
            let ret_ty = InferType::Var(ctx.fresh_meta());
            for case in &lambda.cases {
                let pattern_ty = pattern(ctx, &case.pattern)?;
                unify(&pattern_ty, &param_ty, ctx.forall_level, case.pattern.span())?;

                let body_ty = infer(ctx, &case.body)?;
                unify(&body_ty, &ret_ty, ctx.forall_level, case.body.span())?;
            }

            InferType::Type(MonoType::function(param_ty, ret_ty))
        }

        Expr::Apply(app) => {
            let target_ty = infer(ctx, &app.target)?;
            let arg_ty = infer(ctx, &app.arg)?;
            let ret_ty = InferType::Var(ctx.fresh_meta());

            // The target of an application should always be a function,
            // so unify the target with a function from the argument type to the return type.
            unify(
                &target_ty,
                &InferType::Type(MonoType::function(
                    arg_ty,
                    ret_ty.clone()
                )),
                ctx.forall_level,
                app.target.span()
            )?;

            ret_ty
        }

        Expr::If(if_else) => {
            let condition_ty = infer(ctx, &if_else.condition)?;
            let if_true_ty = infer(ctx, &if_else.if_true)?;
            let if_false_ty = infer(ctx, &if_else.if_false)?;

            unify(
                &condition_ty,
                &InferType::Type(MonoType::Primitive(Primitive::Bool)),
                ctx.forall_level,
                if_else.condition.span()
            )?;

            unify(
                &if_true_ty,
                &if_false_ty,
                ctx.forall_level,
                TextSpan::between(
                    if_else.if_true.span(),
                    if_else.if_false.span()
                )
            )?;

            if_true_ty.clone()
        }
    };

    ctx.add_expr_ty(expr.id(), ty.clone()).unwrap();

    Ok(ty)
}

/// Infers the suggested type of a pattern.
fn pattern(ctx: &Context, pattern: &Pattern<Sem>) -> InferResult<InferType> {
    let ty = match pattern {
        // Wildcard patterns don't suggest any type in particular, so just return a fresh type variable.
        Pattern::Wildcard(_) => InferType::Var(ctx.fresh_meta()),

        // Same as above with variables, they don't suggest any type in particular.
        Pattern::Var(var) => {
            let meta_var = ctx.fresh_meta();
            ctx.add_symbol_ty(var.symbol, PolyType::Type(InferType::Var(meta_var.clone()))).unwrap();
            InferType::Var(meta_var)
        }

        Pattern::Unit(_) => InferType::Type(MonoType::Primitive(Primitive::Unit)),
        Pattern::Number(_) => InferType::Type(MonoType::Primitive(Primitive::Int)),
        Pattern::Bool(_) => InferType::Type(MonoType::Primitive(Primitive::Bool)),
    };

    Ok(ty)
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
    bindings: &'a HashMap<Symbol, GraphNode>,
    graph: &'a mut DiGraph<Symbol, ()>,
}

impl Visitor for Referencer<'_> {
    fn visit(&mut self, item: &dyn visit::Drive) {
        visit!(self, item; VarExpr<Sem>);
    }
}

impl VisitT<VarExpr<Sem>> for Referencer<'_> {
    fn visit_t(&mut self, item: &VarExpr<Sem>) {
        if let Some(referenced) = self.bindings.get(&item.symbol) {
            self.graph.add_edge(self.current, *referenced, ());
        }
    }
}

/// Constructs a graph of references between top-level bindings.
fn reference_graph(ast: &Ast<Sem>) -> DiGraph<Symbol, ()> {
    let mut graph = DiGraph::new();

    let items = &ast.root().0;

    let mut bindings = HashMap::new();
    for item in items {
        match item {
            Item::Binding(binding) => {
                let index = graph.add_node(binding.symbol);
                bindings.insert(binding.symbol, index);
            }
        }
    }

    for item in items {
        match item {
            Item::Binding(binding) => {
                let mut referencer = Referencer {
                    current: *bindings.get(&binding.symbol).unwrap(),
                    bindings: &bindings,
                    graph: &mut graph
                };
                referencer.visit(binding);
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

    pub fn ast(&self, ast: &Ast<Sem>) -> Ast<Typed> {
        let typed_root = self.root(ast.root());

        let typed_symbols = ast.symbols()
            .map(|symbol, data| self.symbol(symbol, data));

        Ast::new(typed_root, typed_symbols)
    }

    fn symbol(&self, symbol: Symbol, data: &SymbolKind<Sem>) -> SymbolKind<Typed> {
        match data {
            SymbolKind::Var(var) => SymbolKind::Var(var.map::<Typed>(|()|
                TypedVariableData {
                    ty: self.get_symbol_type(symbol)
                }
            )),
            SymbolKind::Binding(function) => SymbolKind::Binding(function.map::<Typed>(|()|
                TypedBindingData {
                    ty: self.get_symbol_type(symbol)
                }
            ))
        }
    }

    fn root(&self, Root(items, node_data): &Root<Sem>) -> Root<Typed> {
        let typed_items = items.iter()
            .map(|item| self.item(item))
            .collect();

        Root(typed_items, *node_data)
    }

    fn item(&self, item: &Item<Sem>) -> Item<Typed> {
        match item {
            Item::Binding(function) => {
                let typed_body = self.expr(&function.body);
                Item::Binding(Binding {
                    data: function.data,
                    body: typed_body,
                    symbol: function.symbol
                })
            }
        }
    }

    fn expr(&self, expr: &Expr<Sem>) -> Expr<Typed> {
        let ty = TypedExprData {
            ty: self.get_expr_type(expr.id())
        };

        match expr {
            Expr::Unit(unit) => Expr::Unit(UnitExpr {
                data: unit.data.with(ty)
            }),
            Expr::Int(int) => Expr::Int(IntExpr {
                data: int.data.with(ty),
                val: int.val
            }),
            Expr::Bool(bool) => Expr::Bool(BoolExpr {
                data: bool.data.with(ty),
                val: bool.val
            }),
            Expr::String(string) => Expr::String(StringExpr {
                data: string.data.with(ty),
                val: string.val.clone()
            }),
            Expr::Var(var) => Expr::Var(VarExpr {
                data: var.data.with(ty),
                symbol: var.symbol
            }),

            Expr::Bind(binding) => Expr::bind(Let {
                data: binding.data.with(ty),
                pattern: compile_pattern(&[&binding.pattern]),
                value: self.expr(&binding.value),
                expr: self.expr(&binding.expr)
            }),

            Expr::Lambda(lambda) => {
                let cases = lambda.cases.iter()
                    .map(|x| &x.pattern)
                    .collect::<Vec<_>>();

                let pattern = compile_pattern(&cases);

                Expr::lambda(Lambda {
                    data: lambda.data.with(ty),
                    cases: Cases {
                        root: pattern,
                        actions: lambda.cases.iter()
                            .map(|x| self.expr(&x.body))
                            .collect()
                    }
                })
            }

            Expr::Apply(application) => Expr::apply(Application {
                data: application.data.with(ty),
                target: self.expr(&application.target),
                arg: self.expr(&application.arg)
            }),

            Expr::If(if_else) => Expr::if_else(IfElse {
                data: if_else.data.with(ty),
                condition: self.expr(&if_else.condition),
                if_true: self.expr(&if_else.if_true),
                if_false: self.expr(&if_else.if_false)
            })
        }
    }
}

/*--------------------*\
|  Core type-checking  |
\*--------------------*/

/// Performs type checking and type inference on all the expressions and bindings of an AST.
pub fn type_check(ast: &Ast<Sem>) -> Result<Ast<Typed>, TypeCheckError> {
    // Fetch the reference graph for the tree and compute the strongly-connected components.
    // This is used to know what groups of top-levels bindings need to be inferred together
    // so that unification variables won't unnecessarily leak from one binding into another.
    let references = reference_graph(ast);
    let scc = tarjan_scc(&references);
    let groups = scc.iter()
        .map(|group| group.iter()
            .map(|index| *references.node_weight(*index).unwrap())
            .collect::<Vec<_>>()
        );

    let raw_ctx = RawContext::new();
    let ctx = Context::new(&raw_ctx);

    let mut binding_vars = HashMap::new();

    for group in groups {
        // Create types for each binding and their parameters
        // so that every binding in the group has a corresponding type when inferring their bodies.
        for item in &group {
            // Make sure that the fresh meta variables do not have level 0.
            let ctx = ctx.extend();

            let binding_var = ctx.fresh_meta();

            binding_vars.insert(*item, binding_var.clone());
            ctx.add_symbol_ty(*item, PolyType::Type(InferType::Var(binding_var))).unwrap();
        }

        // Infer the bodies of each binding.
        for item in &group {
            let decl = ast.symbols().get(*item).decl();
            let binding = &ast.get_node_as::<Binding<Sem>>(decl).unwrap();

            let ctx = ctx.extend();

            let body_ty = infer(&ctx, &binding.body)?;

            let binding_var = binding_vars.get(item).unwrap().clone();

            // Important that the level here is 1,
            // since unification variables declared at the top-level
            // would otherwise not be able to have their levels lowerd properly.
            unify(&body_ty, &InferType::Var(binding_var), 1, binding.body.span())?;
        }

        // Try to generalize the binding types.
        for item in &group {
            let binding_var = binding_vars.get(item).unwrap().clone();

            // If we can generalize the binding type then replace the type in the context for further use.
            // Otherwise, the type can just be used as-is since it doesn't contain any unsolved unification variables.
            if let Ok(general) = generalize(&ctx, InferType::Var(binding_var)) {
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
    Ok(embedder.ast(ast))
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
