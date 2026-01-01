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

/// Data for a symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum SymbolData<S: Stage> {
    /// A variable.
    Var(VariableData<S>),
    /// A function.
    Func(FunctionData<S>),
}

/// Data for a variable symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct VariableData<S: Stage> {
    /// The name of the variable.
    pub name: String,
    /// The ID of the declaring node of the variable.
    pub decl: NodeId,
    /// Stage-specific additional for the variable.
    pub data: S::VarData,
}

impl<S: Stage> VariableData<S> {
    pub fn map<T: Stage>(&self, f: impl FnOnce(&S::VarData) -> T::VarData) -> VariableData<T> {
        VariableData {
            name: self.name.clone(),
            decl: self.decl,
            data: f(&self.data)
        }
    }
}

/// Data for a function symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct FunctionData<S: Stage> {
    /// The name of the function.
    pub name: String,
    /// The ID of the declaring node of the function.
    pub decl: NodeId,
    /// Stage-specific additional for the function.
    pub data: S::FuncData,
}

impl<S: Stage> FunctionData<S> {
    pub fn map<T: Stage>(&self, f: impl FnOnce(&S::FuncData) -> T::FuncData) -> FunctionData<T> {
        FunctionData {
            name: self.name.clone(),
            decl: self.decl,
            data: f(&self.data)
        }
    }
}

impl<S: Stage> SymbolData<S> {
    /// Gets the name of the symbol.
    pub fn name(&self) -> &String {
        match self {
            SymbolData::Var(variable) => &variable.name,
            SymbolData::Func(function) => &function.name,
        }
    }

    pub fn decl(&self) -> NodeId {
        match self {
            SymbolData::Var(variable) => variable.decl,
            SymbolData::Func(function) => function.decl,
        }
    }
}

/// Contains mappings between [`Symbol`]s and [`SymbolData`].
#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct Symbols<S: Stage> {
    data: HashMap<Symbol, SymbolData<S>>,
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
    pub fn get(&self, symbol: Symbol) -> &SymbolData<S> {
        self.data.get(&symbol)
            .expect("symbol ID should be valid")
    }

    /// Registers data for a new symbol and returns it.
    pub fn register(&mut self, data: SymbolData<S>) -> Symbol {
        let symbol = SYMBOL_PROVIDER.next();
        self.data.insert(symbol, data);
        symbol
    }

    pub fn map<T: Stage>(&self, mut f: impl FnMut(Symbol, &SymbolData<S>) -> SymbolData<T>) -> Symbols<T> {
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
