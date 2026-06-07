//! Type checking and inference.
//!
//! The algorithm used for type inference is [Algorithm-J](https://en.wikipedia.org/wiki/Hindley-Milner_type_system#Algorithm_J)
//! with bidirectionality tacked on, with the implementation heavily referencing
//! [brendanzab's Language Garden project](https://github.com/brendanzab/language-garden/blob/main/scraps/check_poly_algorithm_j.ml)
//! and [an example by jfetcher](https://github.com/jfecher/algorithm-j).
//! The concept of provenance, lifted from [*Getting into the Flow*](https://dl.acm.org/doi/10.1145/3622812),
//! is additionally used to provide better inference error messages.
//!
//! Most notably, Algorithm-J uses mutable unification variables instead of a substitution map,
//! so [MetaVar] is implemented using interior mutability.

use std::collections::{HashMap, HashSet};

use crate::{
    diagnostic::Diagnostic,
    select_nodes,
    symbols::{Symbol, Symbols},
    syntax::nodes::{Binding, Expr, Item, Pattern, Root, TyExpr, VarExpr},
    types::{
        ForallType, FunctionType, MetaVar, MonoType, PolyType, PrimitiveType, Provenance, Ty,
        TypeVar,
    },
};
use context::Context;
use petgraph::{algo::tarjan_scc, graph::DiGraph};
use slotmap::SparseSecondaryMap;

mod context;

/*---------------------------------*\
|  Type substitution/instantiation  |
\*---------------------------------*/

impl MonoType {
    /// Substitutes type variables within the type for other types.
    pub fn substitute(&self, subs: &HashMap<TypeVar, MonoType>) -> Self {
        match self {
            MonoType::Primitive(prim) => prim.clone().into(),
            MonoType::Function(Ty {
                ty: fun,
                provenance,
            }) => MonoType::Function(Ty {
                ty: Box::new(fun.substitute(subs)),
                provenance: provenance.clone(),
            }),
            MonoType::Var(var) => match subs.get(&var.ty) {
                Some(t) => t.clone(),
                None => var.clone().into(),
            },
            MonoType::Meta(meta) => match meta.get_sub() {
                Some(sub) => sub.clone(),
                None => meta.clone().into(),
            },
            MonoType::Hole => MonoType::Hole,
        }
    }
}

impl FunctionType {
    pub fn substitute(&self, subs: &HashMap<TypeVar, MonoType>) -> Self {
        Self {
            param: self.param.clone().substitute(subs),
            ret: self.ret.clone().substitute(subs),
        }
    }
}

impl ForallType {
    pub fn instantiate(&self, ctx: &Context) -> MonoType {
        let subs = self
            .vars
            .iter()
            .map(|var| (*var, MonoType::Meta(ctx.fresh_meta())))
            .collect::<HashMap<_, _>>();

        self.generalized.clone().substitute(&subs)
    }
}

/*------------*\
|  Algorithms  |
\*------------*/

fn generate_type(ctx: &Context, tyexpr: TyExpr) -> PolyType {
    match tyexpr {
        TyExpr::Unit(tyexpr) => PolyType::Type(MonoType::Primitive(Ty {
            ty: PrimitiveType::Unit,
            provenance: Provenance::Annotation(tyexpr.id()),
        })),

        TyExpr::Int(tyexpr) => PolyType::Type(MonoType::Primitive(Ty {
            ty: PrimitiveType::Int,
            provenance: Provenance::Annotation(tyexpr.id()),
        })),

        TyExpr::Bool(tyexpr) => PolyType::Type(MonoType::Primitive(Ty {
            ty: PrimitiveType::Bool,
            provenance: Provenance::Annotation(tyexpr.id()),
        })),

        TyExpr::String(tyexpr) => PolyType::Type(MonoType::Primitive(Ty {
            ty: PrimitiveType::String,
            provenance: Provenance::Annotation(tyexpr.id()),
        })),

        TyExpr::Var(var) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            PolyType::Type(MonoType::Var(Ty {
                ty: TypeVar::Declared(symbol),
                provenance: Provenance::Annotation(var.id()),
            }))
        }

        TyExpr::Function(function) => {
            let param = prohibit_forall(ctx, generate_type(ctx, function.param()));
            let ret = prohibit_forall(ctx, generate_type(ctx, function.ret()));

            PolyType::Type(MonoType::Function(Ty {
                ty: Box::new(FunctionType { param, ret }),
                provenance: Provenance::Annotation(function.id()),
            }))
        }

        TyExpr::Forall(forall_expr) => {
            let vars = forall_expr
                .vars()
                .map(|var_expr| ctx.symbols().bound(var_expr).unwrap().key())
                .map(TypeVar::Declared);

            let generalized = prohibit_forall(ctx, generate_type(ctx, forall_expr.subty()));

            let forall = ForallType {
                vars: vars.collect(),
                generalized,
            };

            if let Err(_index) = ensure_vars_used(&forall) {
                todo!();
            }

            PolyType::Forall(Ty {
                ty: forall,
                provenance: Provenance::Annotation(forall_expr.id()),
            })
        }

        TyExpr::Grouping(grouping) => generate_type(ctx, grouping.ty()),
    }
}

fn ensure_vars_used(forall: &ForallType) -> Result<(), usize> {
    fn go(ty: &MonoType, used: &mut HashSet<TypeVar>) {
        match ty {
            MonoType::Primitive(_) => {}
            MonoType::Function(Ty { ty: function, .. }) => {
                go(&function.param, used);
                go(&function.ret, used);
            }
            MonoType::Var(Ty { ty: var, .. }) => {
                used.insert(*var);
            }
            MonoType::Meta(meta_var) if let Some(ty) = meta_var.get_sub() => {
                go(ty, used);
            }
            MonoType::Meta(_) | MonoType::Hole => {}
        }
    }

    let mut used = HashSet::new();
    go(&forall.generalized, &mut used);

    for (index, var) in forall.vars.iter().enumerate() {
        if !used.contains(var) {
            return Err(index);
        }
    }

    Ok(())
}

fn prohibit_forall(_ctx: &Context, _ty: PolyType) -> MonoType {
    todo!()
}

fn _occurs(_var: &MetaVar, _within: &MonoType) -> bool {
    todo!()
}

fn _lower(_ty: &MonoType, _level: usize) {
    todo!()
}

fn unify(_a: &MonoType, _b: &MonoType, _level: usize) {
    todo!()
}

fn _generalize(_ctx: &Context, _ty: MonoType) -> Option<Ty<ForallType>> {
    todo!()
}

fn infer(_ctx: &Context, _expr: Expr) -> MonoType {
    todo!()
}

fn check(_ctx: &Context, _expr: Expr, _expected: &MonoType) {
    todo!()
}

fn check_forall(_ctx: &Context, _expr: Expr, _expected: &Ty<ForallType>) {
    todo!()
}

fn _match_inferred_pattern(_ctx: &Context, _pat: Pattern, _expr: Expr) -> PolyType {
    todo!()
}

fn _infer_pattern(_ctx: &Context, _pat: Pattern) -> MonoType {
    todo!()
}

enum _InferredPatternStructure {}

fn _infer_pattern_structure(_ctx: &Context, _pat: Pattern) -> _InferredPatternStructure {
    todo!()
}

fn _check_pattern(_ctx: &Context, _pat: Pattern, _expected: &MonoType) {
    todo!()
}

fn _check_pattern_forall(_ctx: &Context, _pat: Pattern, _expected: &ForallType) {
    todo!()
}

fn _prune(_ty: &MonoType) -> MonoType {
    todo!()
}

/*-------------------*\
|  Reference tracing  |
\*-------------------*/

/// Constructs a graph of references between top-level bindings.
fn reference_graph<'a>(roots: &[Root<'a>], symbols: &Symbols) -> DiGraph<Binding<'a>, ()> {
    let mut graph = DiGraph::new();

    let bindings = roots.iter().flat_map(|root| {
        root.items().map(|item| match item {
            Item::Binding(binding) => binding,
        })
    });

    let binding_indices = bindings
        .clone()
        .map(|binding| (binding, graph.add_node(binding)))
        .collect::<HashMap<_, _>>();

    for binding in bindings {
        let referenced_bindings = select_nodes!(binding => VarExpr)
            .map(|var| symbols.bound(var).unwrap().decl().node)
            .filter_map(|ref_id| Binding::new(binding.raw().map().get(ref_id)));

        for refd in referenced_bindings {
            graph.add_edge(
                *binding_indices.get(&binding).unwrap(),
                *binding_indices.get(&refd).unwrap(),
                (),
            );
        }
    }

    graph
}

/*--------------------*\
|  Core type-checking  |
\*--------------------*/

/// Type-checks a set of roots, returning a map between top-level bindings and their types, as well as a list of diagnostics.
pub fn type_check(
    roots: &[Root],
    symbols: &Symbols,
) -> (SparseSecondaryMap<Symbol, PolyType>, Vec<Diagnostic>) {
    // Fetch the reference graph for the tree and compute the strongly-connected components.
    // This is used to know what groups of top-levels bindings need to be inferred together
    // so that unification variables won't unnecessarily leak from one binding into another.
    let references = reference_graph(roots, symbols);
    let scc = tarjan_scc(&references);
    let groups = scc.iter().map(|group| {
        group
            .iter()
            .map(|index| *references.node_weight(*index).unwrap())
            .collect::<Vec<_>>()
    });

    let ctx = Context::new(symbols);

    let mut binding_vars = HashMap::new();

    for group in groups {
        // Split the bindings in the group into one set of annotated and one set of inferred bindings.
        let mut annotated = Vec::new();
        let mut inferred = group;
        inferred.retain(|binding| {
            if let Some(ann) = binding.ty_ann() {
                annotated.push((*binding, ann));
                false
            } else {
                true
            }
        });

        // Create types for each inferred binding and their parameters
        // so that every binding in the group has a corresponding type when inferring their bodies.
        for binding in &inferred {
            // Make sure that the fresh meta variables do not have level 0.
            let ctx = ctx.extend();

            let binding_var = ctx.fresh_meta();

            binding_vars.insert(*binding, binding_var.clone());
            let symbol = symbols.bound(*binding).unwrap().key();
            ctx.add_symbol_type(symbol, PolyType::Type(MonoType::Meta(binding_var)))
                .unwrap();
        }

        // Begin by checking all bindings with explicit type annotations.
        for (binding, ann) in &annotated {
            let ann = generate_type(&ctx, ann.ty());

            // Important that we register the annotated type as the type of the symbol
            // before inferring the body because otherwise the binding could not reference itself.
            let symbol = symbols.bound(*binding).unwrap().key();
            ctx.add_symbol_type(symbol, ann.clone()).unwrap();

            let ctx = ctx.extend();

            match &ann {
                PolyType::Forall(forall) => check_forall(&ctx, binding.expr(), forall),
                PolyType::Type(ty) => check(&ctx, binding.expr(), ty),
            }
        }

        // Infer the bodies of each binding.
        for binding in &inferred {
            let ctx = ctx.extend();

            let expr_ty = infer(&ctx, binding.expr());

            let binding_var = binding_vars.get(binding).unwrap().clone();

            // Important that the level here is 1,
            // since unification variables declared at the top-level
            // would otherwise not be able to have their levels lowerd properly.
            unify(&expr_ty, &MonoType::Meta(binding_var), 1);
        }

        // Try to generalize the binding types.
        for binding in &inferred {
            let binding_var = binding_vars.get(binding).unwrap().clone();

            // If we can generalize the binding type then replace the type in the context for further use.
            // Otherwise, the type can just be used as-is since it doesn't contain any unsolved unification variables.
            if let Some(general) = _generalize(&ctx, MonoType::Meta(binding_var)) {
                let symbol = symbols.bound(*binding).unwrap().key();
                ctx.replace_symbol_type(symbol, PolyType::Forall(general));
            }
        }
    }

    ctx.into_contents().expect("there shouldn't be any additional alive references to the inference context after inference is complete")
}

#[cfg(test)]
mod tests {
    use insta::assert_yaml_snapshot;
    use std::collections::HashMap;

    use super::*;
    use crate::{
        diagnostic::Diagnostic,
        symbols::{Symbols, resolve_symbols},
        syntax::{Nodes, nodes::Root, parse::test_parse},
        types::PolyType,
    };

    fn test_type_check<'map>(
        nodes: &'map mut Nodes,
        symbols: &mut Symbols,
        text: &str,
    ) -> (Root<'map>, HashMap<String, PolyType>, Vec<Diagnostic>) {
        let (sources, root) = test_parse(nodes, text).unwrap();
        resolve_symbols(symbols, &sources, root).unwrap();
        let (symbol_types, diagnostics) = type_check(&[root], symbols);

        // Returning a map between names and types is far more ergonomic for test code.
        let mut named_types = HashMap::new();
        for (symbol, ty) in symbol_types.into_iter() {
            let result = named_types.insert(symbols.get(symbol).name().to_owned(), ty);
            if result.is_some() {
                panic!("test code should not contain multiple symbols with the same name");
            }
        }

        (root, named_types, diagnostics)
    }

    #[test]
    fn generalize_self_contained() {
        let mut nodes = Nodes::new();
        let mut symbols = Symbols::new();

        let text = "let id = fun x -> x";
        let (_, types, diagnostics) = test_type_check(&mut nodes, &mut symbols, text);

        assert!(diagnostics.is_empty());
        assert_yaml_snapshot!(types.get("id").unwrap());
    }

    #[test]
    fn generalize_mutually_recursive() {
        let mut nodes = Nodes::new();
        let mut symbols = Symbols::new();

        let text = r"
            let a = fun () -> b ()
            let b = fun () -> a ()
        ";
        let (_, types, diagnostics) = test_type_check(&mut nodes, &mut symbols, text);

        assert!(diagnostics.is_empty());
        assert_yaml_snapshot!(types.get("a").unwrap());
        assert_yaml_snapshot!(types.get("b").unwrap());
    }
}
