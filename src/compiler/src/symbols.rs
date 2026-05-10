//! Symbols and semantic resolution.
//!
//! A symbol is a single named semantic element, for instance a variable.
//! Like with syntax nodes, the main type passed around the compiler is [Symbol]
//! which is just an ID for a symbol, while [Symbols] is the central storage for symbols.

use slotmap::{SlotMap, SparseSecondaryMap, new_key_type, sparse_secondary::Entry};

use crate::{
    syntax::{NodeId, SyntaxNode},
    text::TextLocation,
};

pub use ref_graph::*;
pub use resolution::*;

mod ref_graph;
mod resolution;

new_key_type! {
    /// A key to a named semantic element.
    pub struct Symbol;
}

/// Information about the declaration of a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Declaration {
    /// The declaring node.
    ///
    /// This is the *concept node*,
    /// not necessarily the [Ident](crate::syntax::nodes::Ident) that is the name of the symbol.
    /// For instance, a binding symbol has a [Binding](crate::syntax::nodes::Binding) as its declaring node.
    pub node: NodeId,
    /// The declaring location.
    ///
    /// This is the location of the token that is the name of the symbol.
    pub location: TextLocation,
}

impl From<SyntaxNode<'_>> for Declaration {
    fn from(value: SyntaxNode<'_>) -> Self {
        Self {
            node: value.id(),
            location: value.location(),
        }
    }
}

/// Data for a symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolData {
    key: Symbol,
    name: String,
    decl: Declaration,
}

impl SymbolData {
    /// Gets the key identifying the symbol.
    pub fn key(&self) -> Symbol {
        self.key
    }

    /// Gets the name of the symbol.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Gets the declaration of the symbol.
    pub fn decl(&self) -> Declaration {
        self.decl
    }
}

/// Container for a set of symbols.
#[derive(Debug)]
pub struct Symbols {
    map: SlotMap<Symbol, SymbolData>,
    bound: SparseSecondaryMap<NodeId, Symbol>,
}

impl Symbols {
    /// Creates a new [Symbols].
    pub fn new() -> Self {
        Self {
            map: SlotMap::with_key(),
            bound: SparseSecondaryMap::new(),
        }
    }

    /// Registers a new symbol.
    pub fn register(&mut self, name: String, decl: Declaration) -> Result<&SymbolData, Symbol> {
        let key = self
            .map
            .insert_with_key(|key| SymbolData { key, name, decl });

        match self.bound.insert(decl.node, key) {
            Some(old) => Err(old),
            None => Ok(self.map.get(key).unwrap()),
        }
    }

    /// Binds a node to an existing symbol.
    pub fn bind(&mut self, node: NodeId, symbol: Symbol) -> Result<(), Symbol> {
        match self.bound.entry(node).unwrap() {
            Entry::Occupied(entry) => Err(*entry.get()),
            Entry::Vacant(entry) => {
                entry.insert(symbol);
                Ok(())
            }
        }
    }

    /// Gets the data for a symbol.
    pub fn get(&self, symbol: Symbol) -> &SymbolData {
        self.map
            .get(symbol)
            .expect("symbol should be valid in symbol map")
    }

    /// Gets the symbol bound to a node.
    pub fn bound(&self, node: NodeId) -> Option<&SymbolData> {
        self.bound.get(node).map(|symbol| self.get(*symbol))
    }
}

impl Default for Symbols {
    fn default() -> Self {
        Self::new()
    }
}
