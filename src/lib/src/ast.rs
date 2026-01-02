//! Abstract syntax tree and nodes.

mod container;
mod tree;
pub mod visit;

use std::any::Any;

use derivative::Derivative;
use crate::{ast::container::RootContainer, id::Id, stage::Stage, text_span::TextSpan};

pub use self::tree::*;

#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct Ast<S: Stage> {
    container: RootContainer<S>,
    symbols: S::Syms,
}

impl<S: Stage + 'static> Ast<S> {
    pub fn new(root: Root<S>, symbols: S::Syms) -> Self {
        Self {
            container: RootContainer::new(root),
            symbols
        }
    }

    pub fn root(&self) -> &Root<S> {
        self.container.root()
    }

    pub fn symbols(&self) -> &S::Syms {
        &self.symbols
    }

    pub fn get_node(&self, id: NodeId) -> &dyn Node {
        self.container.get_node(id)
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

/// An AST node type.
pub trait Node: Any {
    /// Gets the node data for the node.
    fn node_data(&self) -> NodeData;

    /// Gets the ID for the node.
    fn id(&self) -> NodeId {
        self.node_data().id
    }

    fn span(&self) -> TextSpan {
        self.node_data().span
    }
}
