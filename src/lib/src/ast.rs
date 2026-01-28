//! Abstract syntax tree and nodes.

mod forest;
mod tree;
pub mod visit;

use std::any::Any;

use derivative::Derivative;
use crate::{ast::visit::Drive, id::Id, stage::Stage, text_span::TextSpan};

pub use self::tree::*;
pub use self::forest::Forest;

#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct Ast<S: Stage> {
    forest: Forest<S>,
    symbols: S::Syms,
    ref_graph: S::RefGraph,
}

impl<S: Stage + 'static> Ast<S> {
    pub fn new(root: Root<S>, symbols: S::Syms, ref_graph: S::RefGraph) -> Self {
        Self::new_with_forest(Forest::new(root), symbols, ref_graph)
    }

    pub fn new_with_forest(forest: Forest<S>, symbols: S::Syms, ref_graph: S::RefGraph) -> Self {
        Self {
            forest,
            symbols,
            ref_graph
        }
    }

    pub fn root(&self) -> &Root<S> {
        self.forest.root()
    }

    pub fn symbols(&self) -> &S::Syms {
        &self.symbols
    }

    pub fn ref_graph(&self) -> &S::RefGraph {
        &self.ref_graph
    }

    pub fn get_node(&self, id: NodeId) -> &dyn Node {
        self.forest.get_node(id)
    }

    pub fn get_node_as<N: Node>(&self, id: NodeId) -> Option<&N> {
        (self.get_node(id) as &dyn Any).downcast_ref()
    }
}

/// An ID for a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NodeId(pub Id);

#[derive(Debug, Clone, Copy)]
pub struct NodeData {
    pub span: TextSpan,
    pub id: NodeId,
}

/// A type which contains a [NodeData].
pub trait ToNodeData {
    /// Gets the node data for the value.
    fn node_data(&self) -> NodeData;

    /// Gets the ID of the value.
    fn id(&self) -> NodeId {
        self.node_data().id
    }

    /// Gets the span of the value.
    fn span(&self) -> TextSpan {
        self.node_data().span
    }
}

impl ToNodeData for NodeData {
    #[inline]
    fn node_data(&self) -> NodeData {
        *self
    }
}

impl ToNodeData for ! {
    fn node_data(&self) -> NodeData {
        unreachable!()
    }
}

/// An AST node type.
pub trait Node: ToNodeData + Drive + Any {}

/// Types might implement [Node].
pub trait AsNode: Any {
    /// Gets the value as a `&dyn Node` if the type implements [Node].
    #[inline]
    fn as_node(&self) -> Option<&dyn Node> {
        None
    }
}

impl<N: Node> AsNode for N {
    #[inline]
    fn as_node(&self) -> Option<&dyn Node> {
        Some(self)
    }
}

impl<T: 'static> AsNode for Vec<T> {}

impl<T: 'static> AsNode for Option<T> {}

impl AsNode for () {}

impl AsNode for ! {}
