use std::{cell::OnceCell, collections::HashMap, fmt::Debug, ptr::NonNull};

use crate::{ast::{Node, NodeId, Root, visit::{Drive, Visitor}}, stage::Stage};

// The value here has to be a pointer instead of a reference
// because we want to have a reference into data owned by the container.
// Lifetimes cannot be bound to a specific field of a struct,
// so we need to circumvent this using pointers.
type Map = HashMap<NodeId, NonNull<dyn Node>>;

/// Container for the root of the AST.
/// Additionally allows fetching references to nodes using IDs.
pub struct RootContainer<S: Stage> {
    root: Root<S>,
    refs: OnceCell<Map>,
}

impl<S: Stage + 'static> RootContainer<S> {
    pub fn new(root: Root<S>) -> Self {
        RootContainer {
            root,
            refs: OnceCell::new()
        }
    }

    pub fn root(&self) -> &Root<S> {
        &self.root
    }

    pub fn get_node(&self, id: NodeId) -> &dyn Node {
        let map = self.refs.get_or_init(|| Self::map_ids(&self.root));
        let ptr = *map.get(&id).unwrap();

        // SAFETY: The pointer was constructed from a reference
        // and the lifetime of the reference is the same as that of the container.
        // This is safe because no exclusive references are given out to either the root or the nodes therein,
        // so they are always safe to alias.
        unsafe { ptr.as_ref() }
    }

    fn map_ids(root: &Root<S>) -> Map {
        let mut mapper = IdMapper(Map::new());
        mapper.visit(root);
        mapper.0
    }
}

impl<S: Stage> Debug for RootContainer<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RootContainer")
            .field(&self.root)
            .finish_non_exhaustive()
    }
}

struct IdMapper(Map);

impl Visitor for IdMapper {
    fn visit(&mut self, item: &dyn Drive) {
        if let Some(node) = item.as_node() {
            self.0.insert(node.id(), NonNull::from_ref(node));
        }
        item.drive(self);
    }
}
