//! Reference cycle detection.
//!
//! Since Struktur is strictly evaluated, reference cycles between top-level bindings are not allowed.
//! ```
//! let a = b
//! let b = a
//! ```
//! This is handled by building a graph of the references between bindings and checking it for cycles.
//!
//! The rules for how said graph is built are a compromise between generality and ease of implementation;
//! a reference is considered "reachable" or "used" if it's not nested within any lambdas,
//! or is nested within any level of function application.
//! This makes `let x = y` and `let x = f (fun _ -> y)` both a usage of `y`,
//! but `let x = fun _ -> y` is not.

use std::{cmp::Ordering, collections::HashMap, error::Error, mem};

use crate::{ast::{Application, Ast, Binding, Item, Lambda, ToNodeData, VarExpr, visit::{Drive, VisitT, Visitor}}, stage::Sem, symbols::{BindingSymbol, Symbol, SymbolKind}, text_span::TextSpan, visit};
use itertools::Itertools;
use miette::{LabeledSpan, Severity};
use petgraph::{algo::tarjan_scc, graph::{DiGraph, NodeIndex}};

#[derive(Debug)]
pub struct Cycle {
    bindings: Vec<Ref>,
}

#[derive(Debug)]
struct Ref {
    binding_name: String,
    binding_span: TextSpan,
    ref_name: String,
    ref_span: TextSpan,
}

impl std::fmt::Display for Cycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Reference cycle detected between top-level bindings ")?;

        let Ref { binding_name: last, .. } = &self.bindings.last().unwrap();
        write!(f, "`{last}`")?;

        for Ref { binding_name: name, .. } in &self.bindings {
            write!(f, " -> `{name}`")?;
        }

        Ok(())
    }
}

impl Error for Cycle {}

impl miette::Diagnostic for Cycle {
    fn severity(&self) -> Option<miette::Severity> {
        Some(Severity::Error)
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new("Top-level bindings have to have a definite evaluation order, and can therefore not contain cyclic dependencies between each other"))
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let labels = self.bindings.iter()
            .flat_map(|r| [
                LabeledSpan::underline(r.binding_span),
                LabeledSpan::new_with_span(
                    Some(format!("`{}` references `{}` here", r.binding_name, r.ref_name)),
                    r.ref_span
                )
            ]);

        Some(Box::new(labels))
    }
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum CycleError {
    #[error("Top-level binding `{name}` is self-referential")]
    SelfReference {
        #[label]
        span: TextSpan,
        #[label("`{}` references itself here", name)]
        ref_span: TextSpan,
        name: String,
    },

    #[error(transparent)]
    #[diagnostic(transparent)]
    Cycle(#[from] Cycle),
}

/// Builds the reference graph between top-level bindings of an AST.
/// Additionally ensures that there are no cyclic dependencies between top-level bindings.
pub fn build_ref_graph(ast: &Ast<Sem>) -> Result<DiGraph<Symbol, ()>, CycleError> {
    let references = reference_graph(ast);
    let scc = tarjan_scc(&references);

    let check = Check {
        references: &references,
        ast
    };

    for group in scc {
        check.check_group(group)?;
    }

    // There's no real need to retain the span of references in the returned graph.
    Ok(references.map_owned(|_, binding| binding, |_, _| ()))
}

type ReferenceGraph = DiGraph<Symbol, TextSpan>;

struct Check<'a> {
    references: &'a ReferenceGraph,
    ast: &'a Ast<Sem>,
}

impl Check<'_> {
    fn get_binding(&self, index: NodeIndex) -> (&BindingSymbol<Sem>, &Binding<Sem>) {
        let symbol = *self.references.node_weight(index).unwrap();
        let symbol = match self.ast.symbols().get(symbol) {
            SymbolKind::Binding(binding) => binding,
            _ => unreachable!()
        };

        let binding = self.ast.get_node_as::<Binding<Sem>>(symbol.decl).unwrap();

        (symbol, binding)
    }

    fn check_group(&self, mut group: Vec<NodeIndex>) -> Result<(), CycleError> {
        // Both self-referential and non-self-referential singular graph nodes
        // are their own strongly connected component, so if the group only contains a single node,
        // we have to manually check if it contains a self-reference. As a consolation prize,
        // though, we can at least report a more descriptive error for self-referential bindings.
        if let [index] = group.as_slice() {
            // if references.contains_edge(*index, *index) {
            if let Some(edge) = self.references.edges_connecting(*index, *index).next() {
                let (symbol, binding) = self.get_binding(*index);

                // TODO: Mega super hack until name spans are preserved after symbol resolution.
                let binding_span = TextSpan::new(binding.span().offset() + 4, symbol.name.len());

                return Err(CycleError::SelfReference {
                    span: binding_span,
                    ref_span: *edge.weight(),
                    name: symbol.name.clone()
                });
            } else {
                return Ok(());
            }
        }

        // Sort the group so that the nodes are in the order of the cycle.
        group.sort_by(|a, b|
            if self.references.contains_edge(*a, *b) { Ordering::Less } else { Ordering::Greater }
        );

        let bindings = group.iter()
            .circular_tuple_windows::<(_, _)>()
            .map(|(index, next)| {
                let (symbol, binding) = self.get_binding(*index);
                let (next_symbol, _) = self.get_binding(*next);

                let edge = self.references.edges_connecting(*index, *next).next().unwrap();
                let ref_span = *edge.weight();

                // TODO: Mega super hack until name spans are preserved after symbol resolution.
                let binding_span = TextSpan::new(binding.span().offset() + 4, symbol.name.len());

                Ref {
                    binding_name: symbol.name.clone(),
                    binding_span,
                    ref_name: next_symbol.name.clone(),
                    ref_span
                }
            });

        Err(CycleError::Cycle(Cycle {
            bindings: bindings.collect()
        }))
    }
}

fn reference_graph(ast: &Ast<Sem>) -> ReferenceGraph {
    let mut graph = DiGraph::new();
    let mut bindings = HashMap::new();

    for item in &ast.root().items {
        match item {
            Item::Binding(binding) => {
                bindings.insert(binding.symbol, graph.add_node(binding.symbol));
            }
        }
    }

    for item in &ast.root().items {
        match item {
            Item::Binding(binding) => {
                let mut make = MakeGraph {
                    graph: &mut graph,
                    bindings: &bindings,
                    binding_node: *bindings.get(&binding.symbol).unwrap(),
                    in_app: false
                };
                make.visit(binding);
            }
        }
    }

    graph
}

struct MakeGraph<'a> {
    graph: &'a mut ReferenceGraph,
    bindings: &'a HashMap<Symbol, NodeIndex>,
    binding_node: NodeIndex,
    in_app: bool,
}

impl<'a> Visitor for MakeGraph<'a> {
    fn visit(&mut self, item: &dyn Drive) {
        visit!(self, item; VarExpr<Sem>, Application<Sem>, Lambda<Sem>);
    }
}

// See module docs for what these rules are.

impl VisitT<VarExpr<Sem>> for MakeGraph<'_> {
    fn visit_t(&mut self, item: &VarExpr<Sem>) {
        if let Some(var_node) = self.bindings.get(&item.symbol) {
            self.graph.add_edge(self.binding_node, *var_node, item.span());
        }
    }
}

impl VisitT<Application<Sem>> for MakeGraph<'_> {
    fn visit_t(&mut self, item: &Application<Sem>) {
        let prev = mem::replace(&mut self.in_app, true);
        item.drive(self);
        self.in_app = prev;
    }
}

impl VisitT<Lambda<Sem>> for MakeGraph<'_> {
    fn visit_t(&mut self, item: &Lambda<Sem>) {
        if self.in_app {
            item.drive(self);
        }
    }
}
