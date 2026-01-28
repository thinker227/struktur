use std::{cell::OnceCell, collections::HashMap, fmt::Debug, marker::PhantomPinned, pin::Pin, ptr::NonNull, rc::Rc};

use crate::{ast::{Node, NodeId, Root, visit::{Drive, Visitor}}, stage::Stage};

/// A "forest" of nodes making up an AST.
// Putting all the data in an `Rc` just allows us to cheaply clone forests,
// and the inability to get a mutable reference to the root isn't a problem since ASTs are entirely immutable.
pub struct Forest<S: Stage>(Rc<Inner<S>>);

struct Inner<S: Stage> {
    // Pin the root so that even if the forest is moved, the pointers in the map are still valid.
    // Funnily enough, because none of the associated types in `Stage` require `Unpin`,
    // `Root` and most other node types do not implement `Unpin` in the first place,
    // but it's better to be explicit and use `PhantomPinned` here just in case.
    root: Pin<Box<(Root<S>, PhantomPinned)>>,
    nodes: OnceCell<NodeMap>,
}

// Hack for circumenting self-referencing. We could use something like Ouroboros for this,
// but untangling the lifetimes which that enforces is far too annoying.
// This feels like a very un-Rust-like solution, but this is my project and this works, so I can't care less.
type NodeMap = HashMap<NodeId, NonNull<dyn Node>>;

impl<S: Stage + 'static> Forest<S> {
    /// Constructs a new [Forest] from a root node.
    pub fn new(root: Root<S>) -> Self {
        Self(Rc::new(Inner {
            root: Box::pin((root, PhantomPinned)),
            nodes: OnceCell::new()
        }))
    }

    /// Gets the root of the tree.
    pub fn root(&self) -> &Root<S> {
        &self.0.root.0
    }

    /// Gets a node with a specified ID.
    ///
    /// # Panics
    /// Panics if no node with the specified ID exists.
    pub fn get_node(&self, id: NodeId) -> &dyn Node {
        let map = self.0.nodes.get_or_init(|| Self::map_ids(self.root()));
        let ptr = *map.get(&id).unwrap();

        // SAFETY:
        // The pointer is constructed from a reference to a node owned by the root,
        // so all the guarantees around pointers (non-null, alignment) that references enforce do hold.
        // The root is pinned, so it cannot move in memory, and the memory each pointer is pointing to
        // is therefore guaranteed to not have been invalidated even if the forest is moved.
        unsafe { ptr.as_ref() }
    }

    fn map_ids(root: &Root<S>) -> NodeMap {
        struct IdMapper(NodeMap);

        impl Visitor for IdMapper {
            fn visit(&mut self, item: &dyn Drive) {
                if let Some(node) = item.as_node() {
                    self.0.insert(node.id(), NonNull::from_ref(node));
                }
                item.drive(self);
            }
        }

        let mut mapper = IdMapper(NodeMap::new());
        mapper.visit(root);
        mapper.0
    }
}

impl<S: Stage> Debug for Forest<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Forest")
            .field(&self.0.root)
            .finish_non_exhaustive()
    }
}

impl<S: Stage> Clone for Forest<S> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
