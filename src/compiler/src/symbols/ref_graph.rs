//! Reference cycle detection.
//!
//! See the docs for `build_reference_graph`.

use std::{cmp::Ordering, collections::HashMap, fmt::Write as _, mem};

use ariadne::Label;
use itertools::Itertools;
use petgraph::{
    algo::tarjan_scc,
    graph::{DiGraph, NodeIndex},
};

use crate::{
    diagnostic::{Category, Code, Diagnostic},
    symbols::{Symbol, SymbolData, Symbols},
    syntax::{
        SyntaxNode,
        nodes::{ApplicationExpr, Binding, LambdaExpr, VarExpr},
    },
    text::TextLocation,
};

pub type RefGraph = DiGraph<Symbol, ()>;

/// Builds the reference graph for a set of top-level bindings.
///
/// Since Struktur is strictly evaluated, reference cycles between top-level bindings are not allowed.
/// ```ignore
/// let a = b
/// let b = a
/// ```
/// This is handled by building a graph of the references between bindings and then checking it for cycles.
///
/// The rules for how said graph is built are a compromise between generality and ease of implementation;
/// a reference is considered "reachable" or "used" if it's not nested within any lambdas
/// or is nested within any level of function application.
/// This makes `let x = y` and `let x = f (fun _ -> y)` both a usage of `y`,
/// but `let x = fun _ -> y` is not.
pub fn build_ref_graph<'a>(
    symbols: &Symbols,
    bindings: impl Iterator<Item = Binding<'a>> + Clone,
) -> Result<RefGraph, Diagnostic> {
    let references = reference_graph(symbols, bindings);
    let scc = tarjan_scc(&references);

    let check = Check {
        references: &references,
        symbols,
    };

    for group in scc {
        check.check_group(group)?;
    }

    // There's no real need to retain the span of references in the returned graph.
    Ok(references.map_owned(|_, binding| binding, |_, _| ()))
}

type InnerRefGraph = DiGraph<Symbol, TextLocation>;

fn reference_graph<'a>(
    symbols: &Symbols,
    bindings: impl Iterator<Item = Binding<'a>> + Clone,
) -> InnerRefGraph {
    let mut graph = DiGraph::new();
    let mut binding_graph_nodes = HashMap::new();

    for binding in bindings.clone() {
        let symbol = symbols.bound(binding.id()).unwrap().key();
        binding_graph_nodes.insert(symbol, graph.add_node(symbol));
    }

    for binding in bindings {
        let symbol = symbols.bound(binding.id()).unwrap().key();
        let mut make = MakeGraph {
            symbols,
            graph: &mut graph,
            bindings: &binding_graph_nodes,
            binding_node: *binding_graph_nodes.get(&symbol).unwrap(),
            in_app: false,
        };
        make.visit(binding.raw());
    }

    graph
}

struct MakeGraph<'a> {
    symbols: &'a Symbols,
    graph: &'a mut InnerRefGraph,
    bindings: &'a HashMap<Symbol, NodeIndex>,
    binding_node: NodeIndex,
    in_app: bool,
}

impl MakeGraph<'_> {
    pub fn visit(&mut self, node: SyntaxNode) {
        // See module docs for what these rules are.

        if let Some(var) = VarExpr::new(node) {
            let symbol = self.symbols.bound(var.id()).unwrap().key();
            if let Some(var_node) = self.bindings.get(&symbol) {
                self.graph
                    .add_edge(self.binding_node, *var_node, var.location());
            }

            return;
        }

        if let Some(application) = ApplicationExpr::new(node) {
            let prev = mem::replace(&mut self.in_app, true);

            for child in application.raw().nodes() {
                self.visit(child);
            }

            self.in_app = prev;

            return;
        }

        if !self.in_app
            && let Some(_) = LambdaExpr::new(node)
        {
            return;
        }

        for child in node.nodes() {
            self.visit(child);
        }
    }
}

struct Check<'a> {
    references: &'a InnerRefGraph,
    symbols: &'a Symbols,
}

impl Check<'_> {
    pub fn check_group(&self, mut group: Vec<NodeIndex>) -> Result<(), Diagnostic> {
        // Both self-referential and non-self-referential singular graph nodes
        // are their own strongly connected component, so if the group only contains a single node,
        // we have to manually check if it contains a self-reference. As a consolation prize,
        // though, we can at least report a more descriptive error for self-referential bindings.
        if let [index] = group.as_slice() {
            if let Some(edge) = self.references.edges_connecting(*index, *index).next() {
                // There is a self-edge, meaning there's a self-reference.
                let symbol = self.get_binding(*index);

                let name = &symbol.name;
                let binding_span = symbol.decl().location;

                return Err(error_self_referential(binding_span, *edge.weight(), name));
            } else {
                // The single group does not contain a self-reference, so everything's alright.
                return Ok(());
            }
        }

        // There's more than two groups, meaning there's a reference cycle.

        // Sort the group so that the nodes are in the order of the cycle.
        group.sort_by(|a, b| {
            if self.references.contains_edge(*a, *b) {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        });

        let bindings = group
            .iter()
            .circular_tuple_windows::<(_, _)>()
            .map(|(index, next)| {
                let symbol = self.get_binding(*index);
                let symbol_next = self.get_binding(*next);

                let edge = self
                    .references
                    .edges_connecting(*index, *next)
                    .next()
                    .unwrap();

                Ref {
                    binding_name: symbol.name.clone(),
                    decl_span: symbol.decl().location,
                    ref_name: symbol_next.name.clone(),
                    ref_span: *edge.weight(),
                }
            })
            .collect::<Vec<_>>();

        Err(error_cycle(&bindings))
    }

    fn get_binding(&self, index: NodeIndex) -> &SymbolData {
        let symbol = *self.references.node_weight(index).unwrap();
        self.symbols.get(symbol)

        // let binding = Binding::new(SyntaxNode::new(self.nodes, symbol.decl.node)).unwrap();

        // symbol
    }
}

fn error_self_referential(span: TextLocation, ref_span: TextLocation, name: &str) -> Diagnostic {
    let code = Code::new(Category::Resolve, 3);
    Diagnostic::error(code, span, |report| {
        report
            .with_message(format!("Top-level binding `{name}` is self-referential"))
            .with_label(Label::new(span).with_message("Declared here").with_order(0))
            .with_label(
                Label::new(ref_span)
                    .with_message(format!("`{name}` references itself here"))
                    .with_order(1),
            )
    })
}

struct Ref {
    binding_name: String,
    decl_span: TextLocation,
    ref_name: String,
    ref_span: TextLocation,
}

fn error_cycle(refs: &[Ref]) -> Diagnostic {
    let last = refs.last().unwrap();

    let mut message = format!(
        "Reference cycle detected between top-level bindings `{}`",
        last.binding_name
    );
    for r in refs {
        write!(message, " -> `{}`", r.binding_name).unwrap();
    }

    let labels = refs.iter().flat_map(|r| {
        [
            Label::new(r.decl_span),
            Label::new(r.ref_span).with_message(format!(
                "`{}` references `{}` here",
                r.binding_name, r.ref_name
            )),
        ]
    });

    let code = Code::new(Category::Resolve, 4);
    Diagnostic::error(code, last.decl_span, |report| {
        report.with_message(message).with_labels(labels)
    })
}
