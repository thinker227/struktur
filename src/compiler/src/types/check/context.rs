use std::{
    cell::{Cell, RefCell},
    fmt::Debug,
    rc::Rc,
};

use slotmap::{SparseSecondaryMap, sparse_secondary::Entry};

use crate::{
    diagnostic::Diagnostic,
    symbols::{Symbol, Symbols},
    types::{MetaVar, PolyType, TypeVar},
};

type Types = SparseSecondaryMap<Symbol, PolyType>;

struct Raw<'a> {
    symbols: &'a Symbols,
    symbol_types: RefCell<Types>,
    diagnostics: RefCell<Vec<Diagnostic>>,
    meta_var_id: Cell<u32>,
    inferred_type_var_id: Cell<usize>,
}

/// A context for type-checking and inference.
/// Keeps track of the types of symbols as well as the current forall level.
///
/// For ease of use, the context utilizes interior mutability for the type mapping,
/// but *not* for the forall level.
#[derive(Clone)]
pub struct Context<'a> {
    forall_level: u32,
    raw: Rc<Raw<'a>>,
}

impl<'a> Context<'a> {
    /// Creates a new empty context with a forall level of 0.
    pub fn new(symbols: &'a Symbols) -> Self {
        Self {
            forall_level: 0,
            raw: Rc::new(Raw {
                symbols,
                symbol_types: RefCell::new(SparseSecondaryMap::new()),
                diagnostics: RefCell::new(Vec::new()),
                meta_var_id: Cell::new(0),
                inferred_type_var_id: Cell::new(0),
            }),
        }
    }

    /// Gets the set of symbols in the context.
    pub fn symbols(&self) -> &'a Symbols {
        self.raw.symbols
    }

    /// Gets the context's forall level.
    ///
    /// Note that this is immutable per context.
    pub fn forall_level(&self) -> u32 {
        self.forall_level
    }

    /// Creates a fresh unification variable with the context's forall level.
    pub fn fresh_meta(&self) -> MetaVar {
        let id = self.raw.meta_var_id.get();
        self.raw.meta_var_id.set(id + 1);

        MetaVar::new(self.forall_level, id)
    }

    /// Creates a fresh inferred type variable.
    pub fn fresh_inferred_var(&self) -> TypeVar {
        let id = self.raw.inferred_type_var_id.get();
        self.raw.inferred_type_var_id.set(id + 1);

        TypeVar::Inferred(id)
    }

    /// Extends the context by increasing the forall level by 1, returning a new context
    /// (though with the same shared type mapping).
    #[must_use = "`extend` returns a new context and does not mutate `self`"]
    pub fn extend(&self) -> Self {
        Self {
            forall_level: self.forall_level + 1,
            raw: self.raw.clone(),
        }
    }

    /// Adds a mapping from a symbol to a type.
    pub fn add_symbol_type(&self, symbol: Symbol, ty: PolyType) -> Result<(), AddSymbolError> {
        let mut borrow = self.raw.symbol_types.borrow_mut();
        let entry = borrow
            .entry(symbol)
            .expect("symbol should still be present in the symbol map");

        match entry {
            Entry::Occupied(_) => Err(AddSymbolError),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Creates or replaces an existing mapping from a symbol to a type.
    pub fn replace_symbol_type(&self, symbol: Symbol, ty: PolyType) {
        let mut borrow = self.raw.symbol_types.borrow_mut();
        borrow.insert(symbol, ty);
    }

    /// Looks up a mapping from a symbol to a type.
    pub fn lookup_symbol_type(&self, symbol: Symbol) -> Option<PolyType> {
        self.raw.symbol_types.borrow().get(symbol).cloned()
    }

    /// Adds a diagnostic.
    pub fn add_diagnostic(&self, diagnostic: Diagnostic) {
        let mut borrow = self.raw.diagnostics.borrow_mut();
        borrow.push(diagnostic);
    }

    /// Gets the accumulated contents of the context.
    ///
    /// Since the context internally uses reference-counting, this method attempts to unwrap the [Rc],
    /// assuming there is only one reference to it. If there is more than one reference to the context,
    /// this method returns [None].
    pub fn into_contents(self) -> Option<(Types, Vec<Diagnostic>)> {
        Rc::into_inner(self.raw)
            .map(|raw| (raw.symbol_types.into_inner(), raw.diagnostics.into_inner()))
    }
}

impl Debug for Context<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("forall_level", &self.forall_level)
            .field("symbol_types", &self.raw.symbol_types)
            .finish_non_exhaustive()
    }
}

/// An error returned by looking up the type of something which doesn't have a registered type.
#[derive(Debug, Clone)]
pub struct AddSymbolError;
