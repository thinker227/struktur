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
    symbols::{Symbol, SymbolKind, Symbols, VariableKind},
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
mod error;

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

/// Generates a type from a type expression.
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

            if let Err(index) = ensure_vars_used(&forall) {
                let ty_span = forall_expr.subty().location();
                let var_span = forall_expr.vars().nth(index).unwrap().location();
                let var = forall.vars[index];
                let symbol = var.symbol().unwrap(); // the variable here should always be declared and have a symbol
                let name = ctx.symbols().get(symbol).name();
                ctx.add_diagnostic(error::unused_type_variable(name, var_span, ty_span));
            }

            PolyType::Forall(Ty {
                ty: forall,
                provenance: Provenance::Annotation(forall_expr.id()),
            })
        }

        TyExpr::Grouping(grouping) => generate_type(ctx, grouping.ty()),
    }
}

/// Ensures that all type variables bound by a forall are used inside the type generalized by the forall.
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

/// Prohibits a forall from occuring in a position where a regular (mono-) type is expected.
fn prohibit_forall(ctx: &Context, ty: PolyType) -> MonoType {
    match ty {
        PolyType::Forall(_) => {
            ctx.add_diagnostic(error::forall_prohibited());

            // Todo: Should this maybe return the generalized type instead of hole?
            // If we did that then it would be possible to have weird errors where a type variable is expected
            // but the type variable is not actually bound by anything since the forall is illegal.
            // Could maybe compromise by substituting all the type variables in the generalized expression
            // with hole, but it's hard to say what the user actually intends when writing an illegal forall.
            MonoType::Hole
        }
        PolyType::Type(ty) => ty,
    }
}

/// Gets a poly type as a mono type or instantiates a forall.
fn get_or_instantiate(ctx: &Context, ty: PolyType) -> MonoType {
    match ty {
        PolyType::Forall(Ty { ty: forall, .. }) => forall.instantiate(ctx),
        PolyType::Type(ty) => ty,
    }
}

/// Checks whether a unification variable occurs within another type.
fn occurs(var: &MetaVar, within: &MonoType) -> bool {
    match within {
        MonoType::Function(Ty { ty: fun, .. }) => occurs(var, &fun.param) || occurs(var, &fun.ret),

        MonoType::Meta(other) => match other.get_sub() {
            Some(sub) => occurs(var, sub),
            // Important that we use `same_as` and not `==` here
            // because we only care about reference equality between unification variables.
            None => other.same_as(var),
        },

        _ => false,
    }
}

/// Attempts to lower the level of any unification variables within a type to a given level.
fn lower(ty: &MonoType, level: u32) {
    match ty {
        MonoType::Function(Ty { ty: fun, .. }) => {
            lower(&fun.param, level);
            lower(&fun.ret, level);
        }

        MonoType::Meta(var) => match var.get_sub() {
            Some(sub) => lower(sub, level),
            None => {
                // We don't actually care about whether lowering the variable succeeds,
                // we just attempt it for every variable in the type.
                _ = var.try_lower_level(level);
            }
        },

        _ => {}
    }
}

/// Attempts to unify two types.
fn unify(a: &MonoType, b: &MonoType, level: u32) {
    match (a, b) {
        // Unifying a unification variable with itself does nothing.
        // Important that we use `same_as` and not `==` here
        // because we only care about reference equality between unification variables.
        (MonoType::Meta(a), MonoType::Meta(b)) if a.same_as(b) => {}

        // Unifying a type variable with itself does nothing.
        (MonoType::Var(Ty { ty: a, .. }), MonoType::Var(Ty { ty: b, .. })) if a == b => {}

        (MonoType::Primitive(Ty { ty: a, .. }), MonoType::Primitive(Ty { ty: b, .. }))
            if a == b => {}

        (MonoType::Function(Ty { ty: a, .. }), MonoType::Function(Ty { ty: b, .. })) => {
            unify(&a.param, &b.param, level);
            unify(&a.ret, &b.ret, level);
        }

        // Unify through solved unification variables.
        (MonoType::Meta(var), ty) if let Some(sub) = var.get_sub() => unify(sub, ty, level),
        (ty, MonoType::Meta(var)) if let Some(sub) = var.get_sub() => unify(ty, sub, level),

        (MonoType::Meta(var), ty) | (ty, MonoType::Meta(var)) => {
            if var.get_sub().is_none() {
                if occurs(var, ty) {
                    todo!("error")
                }

                lower(ty, level);

                if !var.sub(ty.clone()) {
                    panic!("{var:?} has already been substituted");
                }
            } else {
                // Already checked for solved unification variables above.
                unreachable!()
            }
        }

        _ => {
            todo!("error")
        }
    }
}

/// Replaces any unsolved unification variables with type variables within a forall generalization.
///
/// Returns [None] if the type does not contain any unsolved unification variables.
fn generalize(
    ctx: &Context,
    provenance: Provenance,
    ty: MonoType,
) -> Result<Ty<ForallType>, MonoType> {
    fn visit(ctx: &Context, provenance: &Provenance, vars: &mut Vec<TypeVar>, ty: &MonoType) {
        match ty {
            MonoType::Function(Ty { ty: fun, .. }) => {
                visit(ctx, provenance, vars, &fun.param);
                visit(ctx, provenance, vars, &fun.ret);
            }

            MonoType::Meta(var) => match var.get_sub() {
                Some(sub) => visit(ctx, provenance, vars, sub),

                None if ctx.forall_level() < var.level() => {
                    let inferred_var = ctx.fresh_inferred_var();
                    var.sub(MonoType::Var(Ty {
                        ty: inferred_var,
                        provenance: Provenance::InferredVar {
                            forall: Box::new(provenance.clone()),
                        },
                    }));
                    vars.push(inferred_var);
                }

                None => {}
            },

            _ => {}
        }
    }

    let mut vars = Vec::new();
    visit(ctx, &provenance, &mut vars, &ty);

    if vars.is_empty() {
        Err(ty)
    } else {
        Ok(Ty {
            ty: ForallType {
                vars,
                generalized: ty,
            },
            provenance: Provenance::Generalize {
                forall: Box::new(provenance),
            },
        })
    }
}

/// Infers the type of an expression.
fn infer(ctx: &Context, expr: Expr) -> MonoType {
    match expr {
        // Primitives are just their respective types.
        Expr::Unit(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::Unit,
            provenance: Provenance::Literal(expr.id()),
        }),
        Expr::Int(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::Int,
            provenance: Provenance::Literal(expr.id()),
        }),
        Expr::Bool(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::Bool,
            provenance: Provenance::Literal(expr.id()),
        }),
        Expr::String(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::String,
            provenance: Provenance::Literal(expr.id()),
        }),

        Expr::Var(var) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            let var_ty = ctx
                .lookup_symbol_type(symbol)
                .expect("variable should have a registered type");

            get_or_instantiate(ctx, var_ty)
        }

        Expr::Let(let_expr) => {
            // Type-check the pattern and value and register its bound variables into the context.
            match_inferred_pattern(ctx, let_expr.pattern(), let_expr.value());

            // Now that we have the types of the variables bound by the binding in the context,
            // we can infer the return expression.
            infer(ctx, let_expr.subexpr())
        }

        Expr::Lambda(lambda_expr) => {
            let param_ty = MonoType::Meta(ctx.fresh_meta());
            let ret_ty = MonoType::Meta(ctx.fresh_meta());

            // Iterate through the lambda cases and successively build up the parameter and return types.
            for case in lambda_expr.cases() {
                let pattern_ty = infer_pattern(ctx, case.pattern());
                unify(&pattern_ty, &param_ty, ctx.forall_level());

                let body_ty = infer(ctx, case.body());
                unify(&body_ty, &ret_ty, ctx.forall_level());
            }

            MonoType::Function(Ty {
                ty: Box::new(FunctionType {
                    param: param_ty,
                    ret: ret_ty,
                }),
                provenance: Provenance::Lambda(lambda_expr.id()),
            })
        }

        Expr::Application(app) => {
            let target_ty = infer(ctx, app.target());
            let arg_ty = infer(ctx, app.arg());
            let ret_ty = MonoType::Meta(ctx.fresh_meta());

            // The target of an application should always be a function,
            // so unify the target with a function from the argument type to the return type.
            unify(
                &target_ty,
                &MonoType::Function(Ty {
                    ty: Box::new(FunctionType {
                        param: arg_ty,
                        ret: ret_ty.clone(),
                    }),
                    provenance: Provenance::Application(app.id()),
                }),
                ctx.forall_level(),
            );

            ret_ty
        }

        Expr::IfElse(if_else) => {
            check(
                ctx,
                if_else.condition(),
                &MonoType::Primitive(Ty {
                    ty: PrimitiveType::Bool,
                    provenance: Provenance::IfCondition(if_else.id()),
                }),
            );

            let true_ty = infer(ctx, if_else.true_branch());
            let false_ty = infer(ctx, if_else.false_branch());

            unify(&true_ty, &false_ty, ctx.forall_level());

            // If inferring the true branch resulted in an error,
            // it's better to use the (hopefully non-erroneous) type of the false branch.
            match true_ty {
                MonoType::Hole => false_ty,
                ty => ty,
            }
        }

        Expr::TyAnn(ann) => {
            let ty = prohibit_forall(ctx, generate_type(ctx, ann.ty_ann().ty()));
            check(ctx, ann.expr(), &ty);
            ty
        }

        Expr::Grouping(group) => infer(ctx, group.expr()),
    }
}

/// Checks that a given expression has an expected type.
fn check(ctx: &Context, expr: Expr, expected: &MonoType) {
    match (expr, expected) {
        (
            Expr::Unit(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::Unit,
                ..
            }),
        )
        | (
            Expr::Int(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::Int,
                ..
            }),
        )
        | (
            Expr::Bool(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::Bool,
                ..
            }),
        )
        | (
            Expr::String(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::String,
                ..
            }),
        ) => {}

        (Expr::Var(var), _) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            let var_ty = ctx
                .lookup_symbol_type(symbol)
                .expect("variable should have a registered type");

            let ty = get_or_instantiate(ctx, var_ty);

            unify(&ty, expected, ctx.forall_level());
        }

        (Expr::Let(let_expr), _) => {
            // Try to infer a polymorphic type from the structure of the pattern.
            // Additionally, this sets the type of all the variables bound by the pattern.
            match_inferred_pattern(ctx, let_expr.pattern(), let_expr.value());

            // Now that we have the types of the variables bound by the binding in the context,
            // we can check the return expression.
            check(ctx, let_expr.subexpr(), expected);
        }

        // If we have a lambda with an expected type that is not a function,
        // then just fall back on the default case which will attempt to unify the two
        // and subsequently fail.
        (Expr::Lambda(lambda), MonoType::Function(Ty { ty: fun, .. })) => {
            for case in lambda.cases() {
                check_pattern(ctx, case.pattern(), &fun.param);
                check(ctx, case.body(), &fun.ret);
            }
        }

        (Expr::Application(app), _) => {
            let target_ty = infer(ctx, app.target());
            let arg_ty = infer(ctx, app.arg());
            let ret_ty = MonoType::Meta(ctx.fresh_meta());

            // The target of an application should always be a function,
            // so unify the target with a function from the argument type to the return type.
            unify(
                &target_ty,
                &MonoType::Function(Ty {
                    ty: Box::new(FunctionType {
                        param: arg_ty,
                        ret: ret_ty.clone(),
                    }),
                    provenance: Provenance::Application(app.id()),
                }),
                ctx.forall_level(),
            );

            unify(&ret_ty, expected, ctx.forall_level());
        }

        (Expr::IfElse(if_else), _) => {
            check(
                ctx,
                if_else.condition(),
                &MonoType::Primitive(Ty {
                    ty: PrimitiveType::Bool,
                    provenance: Provenance::IfCondition(if_else.id()),
                }),
            );

            check(ctx, if_else.true_branch(), expected);
            check(ctx, if_else.false_branch(), expected);
        }

        (Expr::TyAnn(ann), _) => {
            // If a type annotation expression is encountered here, then the annotated
            // type has to be the same as the currently expected type.
            // It also cannot be a forall since expressions cannot have forall types.
            let ann_ty = prohibit_forall(ctx, generate_type(ctx, ann.ty_ann().ty()));

            if &ann_ty != expected {
                todo!("error")
            }

            check(ctx, ann.expr(), expected);
        }

        (Expr::Grouping(grouping), _) => check(ctx, grouping.expr(), expected),

        _ => {
            // Fall back on unification.
            let ty = infer(ctx, expr);
            unify(&ty, expected, ctx.forall_level());
        }
    }
}

/// Checks that a given expression has an expected forall type.
fn check_forall(ctx: &Context, expr: Expr, expected: &Ty<ForallType>) {
    // There's no way that an expression is expected to have a forall type without an explicit type annotation,
    // in which case there also cannot be any meta variables inside the type.
    check(ctx, expr, &expected.ty.generalized)
}

/// Infers the type of a pattern.
fn infer_pattern(ctx: &Context, pat: Pattern) -> MonoType {
    match pat {
        // Wildcard patterns don't suggest any type in particular, so just return a fresh type variable.
        Pattern::Wildcard(_) => MonoType::Meta(ctx.fresh_meta()),

        // Same as above with variables, they don't suggest any type in particular.
        Pattern::Var(var) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            let meta_var = ctx.fresh_meta();
            let ty = MonoType::Meta(meta_var);
            ctx.add_symbol_type(symbol, PolyType::Type(ty.clone()))
                .unwrap();
            ty
        }

        Pattern::Unit(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::Unit,
            provenance: Provenance::LiteralPattern(pat.id()),
        }),
        Pattern::Number(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::Int,
            provenance: Provenance::LiteralPattern(pat.id()),
        }),
        Pattern::Bool(_) => MonoType::Primitive(Ty {
            ty: PrimitiveType::Bool,
            provenance: Provenance::LiteralPattern(pat.id()),
        }),

        Pattern::TyAnn(ann) => {
            let ty = prohibit_forall(ctx, generate_type(ctx, ann.ty_ann().ty()));
            check_pattern(ctx, ann.pattern(), &ty);
            ty
        }

        Pattern::Grouping(group) => infer_pattern(ctx, group.pattern()),
    }
}

/// The inferred structure of a pattern.
enum InferredPatternStructure {
    /// The pattern is *able* to be generalized, but isn't explicitly annotated with a forall type.
    Generalizable(MetaVar, Option<Symbol>, Provenance),
    /// The pattern is explicitly annotated as a forall type.
    Forall(Ty<ForallType>),
    /// The pattern is explicitly annotated as something other than a forall type.
    Annotated(MonoType),
    /// The pattern's says nothing explicitly about its type.
    Inferred(MonoType),
}

/// Infers the structure of a pattern in a position where a generalization may occur.
fn infer_pattern_structure(ctx: &Context, pat: Pattern) -> InferredPatternStructure {
    match pat {
        // Wildcard- and variable patterns can both be generalized.
        Pattern::Wildcard(_) => InferredPatternStructure::Generalizable(
            ctx.fresh_meta(),
            None,
            Provenance::WildcardPattern(pat.id()),
        ),
        Pattern::Var(var) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            InferredPatternStructure::Generalizable(
                ctx.fresh_meta(),
                Some(symbol),
                Provenance::VarPattern(pat.id()),
            )
        }

        Pattern::TyAnn(ann) => match generate_type(ctx, ann.ty_ann().ty()) {
            PolyType::Forall(forall) => {
                check_pattern_forall(ctx, ann.pattern(), &forall);
                InferredPatternStructure::Forall(forall)
            }
            PolyType::Type(ty) => {
                check_pattern(ctx, ann.pattern(), &ty);
                InferredPatternStructure::Annotated(ty)
            }
        },

        Pattern::Grouping(group) => infer_pattern_structure(ctx, group.pattern()),

        Pattern::Unit(_) | Pattern::Number(_) | Pattern::Bool(_) => {
            let ty = infer_pattern(ctx, pat);
            InferredPatternStructure::Inferred(ty)
        }
    }
}

/// Type-checks the inferred structure of a pattern against an expression.
fn match_inferred_pattern(ctx: &Context, pat: Pattern, expr: Expr) -> PolyType {
    match infer_pattern_structure(ctx, pat) {
        // The pattern's type is able to be generalized.
        InferredPatternStructure::Generalizable(meta_var, symbol, provenance) => {
            // Infer the type of the value and try to generalize it.
            let val_ty = infer(&ctx.extend(), expr);
            let (var_ty, generalized) = match generalize(ctx, provenance, val_ty) {
                Ok(forall) => {
                    let generalized = forall.ty.generalized.clone();
                    (PolyType::Forall(forall), generalized)
                }
                Err(ty) => (PolyType::Type(ty.clone()), ty),
            };

            if !meta_var.sub(generalized) {
                panic!(
                    "meta variable returned from infer_pattern_poly should not be substituted already"
                );
            }

            if let Some(symbol) = symbol {
                ctx.add_symbol_type(symbol, var_ty).unwrap();
            }

            PolyType::Type(MonoType::Meta(meta_var))
        }

        // The pattern was annotated with some type, so we have to check that the type of the value matches that.
        // Either an explicit forall...
        InferredPatternStructure::Forall(forall) => {
            check_forall(ctx, expr, &forall);

            PolyType::Forall(forall)
        }
        // ... or just a normal type.
        InferredPatternStructure::Annotated(ty) => {
            check(ctx, expr, &ty);

            PolyType::Type(ty)
        }

        // The pattern's structure said nothing about its type.
        // Just infer as normal and unify with the type of the value.
        InferredPatternStructure::Inferred(pat_ty) => {
            let val_ty = infer(ctx, expr);
            unify(&val_ty, &pat_ty, ctx.forall_level());

            PolyType::Type(pat_ty)
        }
    }
}

/// Checks that a given pattern matches an expected type.
fn check_pattern(ctx: &Context, pat: Pattern, expected: &MonoType) {
    match (pat, expected) {
        // Everything matches a wildcard.
        (Pattern::Wildcard(_), _) => {}

        (Pattern::Var(var), _) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            ctx.add_symbol_type(symbol, PolyType::Type(expected.clone()))
                .unwrap();
        }

        (
            Pattern::Unit(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::Unit,
                ..
            }),
        )
        | (
            Pattern::Number(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::Int,
                ..
            }),
        )
        | (
            Pattern::Bool(_),
            MonoType::Primitive(Ty {
                ty: PrimitiveType::Bool,
                ..
            }),
        ) => {}

        (Pattern::TyAnn(ann), _) => {
            let ty = prohibit_forall(ctx, generate_type(ctx, ann.ty_ann().ty()));
            check_pattern(ctx, ann.pattern(), &ty);
            unify(&ty, expected, ctx.forall_level());
        }

        (Pattern::Grouping(group), _) => check_pattern(ctx, group.pattern(), expected),

        _ => {
            // Fall back on unification.
            let ty = infer_pattern(ctx, pat);
            unify(&ty, expected, ctx.forall_level());
        }
    }
}

fn check_pattern_forall(ctx: &Context, pat: Pattern, expected: &Ty<ForallType>) {
    match pat {
        Pattern::Wildcard(_) => {}

        Pattern::Var(var) => {
            let symbol = ctx.symbols().bound(var).unwrap().key();
            let forall = expected.clone();
            ctx.add_symbol_type(symbol, PolyType::Forall(forall))
                .unwrap();
        }

        Pattern::TyAnn(ann) => {
            let ty = generate_type(ctx, ann.ty_ann().ty());

            // Type annotations only count here if the annotated type is the exact same forall type.
            // TODO: This needs to be structural, different foralls have technically different type variable symbols but can still be structurally equal.
            if let PolyType::Forall(ref forall) = ty
                && forall == expected
            {
            } else {
                todo!("error");
            }
        }

        Pattern::Grouping(group) => check_pattern_forall(ctx, group.pattern(), expected),

        _ => {
            todo!("error");
        }
    }
}

impl MonoType {
    /// Prunes away all the unification variables from a type.
    fn _prune(self) -> Self {
        match self {
            MonoType::Primitive(primitive) => MonoType::Primitive(primitive),

            MonoType::Function(ty) => MonoType::Function(ty.map(|deref!(fun)| {
                Box::new(FunctionType {
                    param: fun.param._prune(),
                    ret: fun.ret._prune(),
                })
            })),

            MonoType::Var(var) => MonoType::Var(var),

            MonoType::Meta(var) => match var.get_sub() {
                Some(ty) => ty.clone()._prune(),
                None => panic!("cannot prune unsubstituted unification variable {var:?}"),
            },

            MonoType::Hole => MonoType::Hole,
        }
    }
}

impl PolyType {
    /// Prunes away all the unification variables from a type.
    fn prune(self) -> Self {
        match self {
            PolyType::Forall(ty) => PolyType::Forall(ty.map(|forall| ForallType {
                generalized: forall.generalized._prune(),
                vars: forall.vars,
            })),
            PolyType::Type(ty) => PolyType::Type(ty._prune()),
        }
    }
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

            let symbol = symbols.bound(*binding).unwrap().key();

            // If we can generalize the binding type then replace the type in the context for further use.
            // Otherwise, the type can just be used as-is since it doesn't contain any unsolved unification variables.
            if let Ok(general) = generalize(
                &ctx,
                Provenance::GeneralizeLet(binding.id()),
                MonoType::Meta(binding_var),
            ) {
                ctx.replace_symbol_type(symbol, PolyType::Forall(general));
            }
        }
    }

    let (mut types, diagnostics) = ctx.into_contents().expect("there shouldn't be any additional alive references to the inference context after inference is complete");

    // Prune the types of all top-level bindings and discard the rest.
    // Technically it's not strictly necessary to discard all the non-bindings,
    // but it's nicer in order to not accidentally leak unification variables.
    types.retain(|symbol, orig| {
        let symbol = symbols.get(symbol);
        if matches!(symbol.kind(), SymbolKind::Variable(VariableKind::Binding)) {
            replace_with::replace_with(
                orig,
                || {
                    // This *should* never happen, but we can't panic here,
                    // so we just do a dirty eprintln to notify if this does happens
                    // and return a dummy value.
                    eprintln!("exceptional non-panicing print: `prune` paniced");
                    PolyType::Type(MonoType::Hole)
                },
                |ty| ty.prune(),
            );

            // Only keep
            true
        } else {
            false
        }
    });

    (types, diagnostics)
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
        let (sources, root, _) = test_parse(nodes, text).unwrap();
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
