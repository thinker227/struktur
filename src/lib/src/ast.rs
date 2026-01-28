//! Abstract syntax tree and nodes.

mod tree;
pub mod visit;

use std::{any::Any, cell::OnceCell, collections::HashMap};

use ouroboros::self_referencing;
use crate::{ast::visit::Drive, id::Id, stage::Stage, text_span::TextSpan};

pub use self::tree::*;

pub struct Ast<S: Stage + 'static> {
    inner: Inner<S>,
    symbols: S::Syms,
}

#[self_referencing]
struct Inner<S: Stage + 'static> {
    root: Root<S>,
    #[borrows(root)]
    #[not_covariant]
    nodes: OnceCell<HashMap<NodeId, &'this dyn Node>>,
}

impl<S: Stage + 'static> Ast<S> {
    pub fn new(root: Root<S>, symbols: S::Syms) -> Self {
        // let make_nodes = |root| {
        //     todo!()
        // };

        Self {
            inner: Inner::new(root, |_| OnceCell::new()),
            symbols
        }
    }

    pub fn root(&self) -> &Root<S> {
        self.inner.borrow_root()
    }

    pub fn symbols(&self) -> &S::Syms {
        &self.symbols
    }

    pub fn get_node_as<N: Node>(&self, id: NodeId) -> Option<&N> {
        (self.get_node(id) as &dyn Any).downcast_ref()
    }

    pub fn get_node(&self, id: NodeId) -> &&dyn Node {
        self.inner.with(|borrow| {
            let map = borrow.nodes.get_or_init(|| Self::build_nodes(borrow.root));
            map.get(&id).unwrap()
        })
    }

    fn build_nodes(root: &Root<S>) -> HashMap<NodeId, &dyn Node> {
        todo!()
    }
}

impl<S: Stage + 'static> std::fmt::Debug for Ast<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ast")
            .field("root", self.inner.borrow_root())
            .field("symbols", &self.symbols).finish()
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
