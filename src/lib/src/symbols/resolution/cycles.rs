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

use std::{collections::HashMap, error::Error, mem};

use crate::{ast::{Application, Ast, Binding, Item, Lambda, ToNodeData, VarExpr, visit::{Drive, VisitT, Visitor}}, stage::Sem, symbols::{Symbol, SymbolKind}, text_span::TextSpan, visit};
use miette::{LabeledSpan, Severity};
use petgraph::{algo::tarjan_scc, graph::{DiGraph, NodeIndex}};

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

fn reference_graph(ast: &Ast<Sem>) -> DiGraph<Symbol, ()> {
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
    graph: &'a mut DiGraph<Symbol, ()>,
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
            self.graph.add_edge(self.binding_node, *var_node, ());
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
