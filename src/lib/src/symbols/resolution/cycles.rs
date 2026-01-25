//! Reference cycle detection.
//!
//! Since Struktur is strictly evaluated, reference cycles between top-level bindings are not allowed.
//! ```ocaml
//! let a = b
//! let b = a
//! ```
//! This is handled by building a graph of the references between bindings
//! and checking it for cycles. This would be simple if it wasn't for the fact that cyclic references
//! deferred by lambdas *are* allowed, so we need a specialized algorithm for building the graph
//! in order to handle this.
//! ```ocaml
//! let a = fun () -> b ()
//! let b = fun () -> a ()
//! ```

use std::{collections::HashMap, error::Error};

use crate::{ast::{Ast, Binding, Expr, Item, ToNodeData}, stage::Sem, symbols::{Symbol, SymbolKind}, text_span::TextSpan};
use miette::{LabeledSpan, Severity};
use petgraph::{algo::tarjan_scc, graph::DiGraph};

#[derive(Debug)]
pub struct CycleError {
    bindings: Vec<(String, TextSpan)>,
}

impl std::fmt::Display for CycleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cycle detected between top-level bindings ")?;

        let (first, _) = &self.bindings[0];
        write!(f, "`{first}`")?;

        for (name, _) in self.bindings.iter().rev() {
            write!(f, " -> `{name}`")?;
        }

        Ok(())
    }
}

impl Error for CycleError {}

impl miette::Diagnostic for CycleError {
    fn severity(&self) -> Option<miette::Severity> {
        Some(Severity::Error)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let labels = self.bindings.iter()
            .map(|(_, span)| LabeledSpan::underline(*span));

        Some(Box::new(labels))
    }
}

type CycleResult<T> = Result<T, CycleError>;

pub fn check_cycles(ast: &Ast<Sem>) -> CycleResult<()> {
    let references = reference_graph(ast);
    let scc = tarjan_scc(&references);

    for group in scc {
        if group.len() <= 1 {
            continue;
        }

        let bindings = group.iter().map(|index| {
            let symbol = *references.node_weight(*index).unwrap();
            let symbol = match ast.symbols().get(symbol) {
                SymbolKind::Binding(binding) => binding,
                _ => unreachable!()
            };

            let binding = ast.get_node_as::<Binding<Sem>>(symbol.decl).unwrap();

            (symbol.name.clone(), binding.span())
        });

        return Err(CycleError {
            bindings: bindings.collect()
        });
    }

    Ok(())
}

fn reference_graph(ast: &Ast<Sem>) -> DiGraph<Symbol, TextSpan> {
    let items = &ast.root().items;

    let mut refs = HashMap::new();
    for item in items {
        match item {
            Item::Binding(binding) => {
                let rs = trace_binding(binding);
                refs.insert(binding.symbol, rs);
            }
        }
    }

    let mut graph = DiGraph::new();

    todo!();

    graph
}

/// A symbol or set of symbols referenced by an expression.
enum Ref {
    /// A reference to a symbol which is plainly used as a value.
    Use(Symbol),
    /// A reference to a symbol and all of its references.
    Transitive(Symbol),
    /// A set of references which are only relevant if invoked.
    Deferred(Vec<Ref>),
}

/// Signifies the context in which an expression is used.
#[derive(Debug, Clone, Copy)]
enum Context {
    /// The expression's value will be used (for instance as the value of a binding).
    Use,
    /// The expression's value will be invoked.
    Invoke,
}

/// Traces the references of a binding.
fn trace_binding(binding: &Binding<Sem>) -> Vec<Ref> {
    let mut refs = Vec::new();
    trace_expr(&binding.body, Context::Use, &mut refs);
    refs
}

/// Traces the references of an expression.
fn trace_expr(expr: &Expr<Sem>, ctx: Context, refs: &mut Vec<Ref>) {
    match expr {
        Expr::Unit(_)
        | Expr::Int(_)
        | Expr::Bool(_)
        | Expr::String(_)
        => {}

        Expr::Var(var) => {
            // If the current context is that of invoking the variable,
            // then all of the variable's references are also references
            // of this expression. Otherwise it's just a normal usage.
            refs.push(match ctx {
                Context::Use => Ref::Use(var.symbol),
                Context::Invoke => Ref::Transitive(var.symbol),
            });
        }

        Expr::Bind(binding) => {
            // Invocation only cascades to the sub-expression of a binding,
            // the value is just *used*.
            trace_expr(&binding.value, Context::Use, refs);
            trace_expr(&binding.expr, ctx, refs);
        }

        Expr::Lambda(lambda) => {
            // The references within lambdas are only relevant if the lambda is invoked.
            // Therefore we collect them into a separate list and put them into a `Deferred` reference.
            let mut sub = Vec::new();
            for case in &lambda.cases {
                trace_expr(&case.body, Context::Use, &mut sub);
            }

            refs.push(Ref::Deferred(sub));
        }

        Expr::Apply(application) => {
            // This is the crux of this algorithm for reference tracing.
            // If we encounter an application, then all of the deferred references
            // of the target expression are relevant to this expression as well.
            // That is to say, if a lambda (which produces deferred references)
            // is invoked, then we are interested in those deferred references.

            let mut sub = Vec::new();
            trace_expr(&application.target, Context::Invoke, &mut sub);

            for r in sub {
                match r {
                    Ref::Use(_) => refs.push(r),
                    Ref::Transitive(_) => refs.push(r),
                    Ref::Deferred(rs) => refs.extend(rs),
                }
            }

            trace_expr(&application.arg, Context::Use, refs);
        }

        Expr::If(if_else) => {
            // Similarly to let-expressions, invocation only cascades to the
            // branch expressions of if-expressions, the condition is just *used*.
            trace_expr(&if_else.condition, Context::Use, refs);
            trace_expr(&if_else.if_true, ctx, refs);
            trace_expr(&if_else.if_false, ctx, refs);
        }

        Expr::TyAnn(tyann) => {
            // Type annotations are transparent.
            trace_expr(&tyann.expr, ctx, refs);
        }
    }
}
