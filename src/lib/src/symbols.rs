#![allow(unused_assignments)]

//! Symbols and semantic resolution.

mod resolution;

use std::collections::HashMap;

use derivative::Derivative;

use crate::id::{Id, IdProvider};
use crate::stage::Stage;
use crate::ast::*;

pub use resolution::{SymbolResError, resolve_symbols};

/// A reference to a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(Id);

impl Symbol {
    #[cfg(test)]
    /// Allows tests to construct symbols for use in "fake" ASTs.
    pub fn next() -> Symbol {
        SYMBOL_PROVIDER.next()
    }
}

static SYMBOL_PROVIDER: IdProvider<Symbol> = IdProvider::new(Symbol);

/// The kind of some symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum SymbolKind<S: Stage> {
    /// A variable.
    Var(VariableSymbol<S>),
    /// A binding.
    Binding(BindingSymbol<S>),
}

/// A variable symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct VariableSymbol<S: Stage> {
    /// The name of the variable.
    pub name: String,
    /// The ID of the declaring node of the variable.
    pub decl: NodeId,
    /// Stage-specific additional for the variable.
    pub data: S::VarData,
}

impl<S: Stage> VariableSymbol<S> {
    pub fn map<T: Stage>(&self, f: impl FnOnce(&S::VarData) -> T::VarData) -> VariableSymbol<T> {
        VariableSymbol {
            name: self.name.clone(),
            decl: self.decl,
            data: f(&self.data)
        }
    }
}

/// A binding symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct BindingSymbol<S: Stage> {
    /// The name of the binding.
    pub name: String,
    /// The ID of the declaring node of the binding.
    pub decl: NodeId,
    /// Stage-specific additional for the binding.
    pub data: S::BindingData,
}

impl<S: Stage> BindingSymbol<S> {
    pub fn map<T: Stage>(&self, f: impl FnOnce(&S::BindingData) -> T::BindingData) -> BindingSymbol<T> {
        BindingSymbol {
            name: self.name.clone(),
            decl: self.decl,
            data: f(&self.data)
        }
    }
}

impl<S: Stage> SymbolKind<S> {
    /// Gets the name of the symbol.
    pub fn name(&self) -> &String {
        match self {
            SymbolKind::Var(variable) => &variable.name,
            SymbolKind::Binding(binding) => &binding.name,
        }
    }

    pub fn decl(&self) -> NodeId {
        match self {
            SymbolKind::Var(variable) => variable.decl,
            SymbolKind::Binding(binding) => binding.decl,
        }
    }
}

/// Contains mappings between [`Symbol`]s and [`SymbolData`].
#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct Symbols<S: Stage> {
    data: HashMap<Symbol, SymbolKind<S>>,
}

impl<S: Stage> Symbols<S> {
    /// Constructs a new [`Symbols`].
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    /// Gets the data for a given symbol.
    ///
    /// # Panics
    /// Panics if the given symbol does not originate from this [`Symbols`].
    pub fn get(&self, symbol: Symbol) -> &SymbolKind<S> {
        self.data.get(&symbol)
            .expect("symbol ID should be valid")
    }

    /// Registers data for a new symbol and returns it.
    pub fn register(&mut self, data: SymbolKind<S>) -> Symbol {
        let symbol = SYMBOL_PROVIDER.next();
        self.data.insert(symbol, data);
        symbol
    }

    pub fn map<T: Stage>(&self, mut f: impl FnMut(Symbol, &SymbolKind<S>) -> SymbolKind<T>) -> Symbols<T> {
        let data = self.data.iter()
            .map(|(symbol, data)| (
                *symbol,
                f(*symbol, data)
            ))
            .collect();

        Symbols {
            data
        }
    }
}
