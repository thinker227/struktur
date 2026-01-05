//! Typed representations of the various stages of compilation.
//!
//! The Struktur compiler follows the model laid out in the paper
//! [Trees that Grow](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf).
//! In essence, the entire Struktur AST and various other items like symbols are all parameterized
//! by a [Stage] type which exposes various associated types for data within the AST.
//! For instance, symbols during parsing are just simple strings,
//! but after symbol resolution they are semantic symbol IDs.
//!
//! The typical compilation pipeline goes
//! ```ignore
//!                         String
//! -> parse()           -> Parse
//! -> resolve_symbols() -> Sem
//! -> type_check()      -> Typed
//! ```

use std::fmt::Debug;

use crate::{ast::{self, visit::Drive}, patterns, symbols::{Symbol, Symbols}, types::{TypedBindingData, TypedExprData, TypedVariableData}};

/// The compilation stage of an AST.
pub trait Stage {
    /// Representation of symbols.
    type Sym: Debug + Clone;

    /// Representation of patterns.
    type Pattern: Debug + Clone + Drive;

    /// Global collection of symbols.
    type Syms: Debug;

    /// Additional data for expressions.
    type ExprData: Debug + Clone;

    /// Additional data for variables.
    type VarData: Debug + Clone;

    /// Additional data for functions.
    type BindingData: Debug + Clone;
}

/// Freshly parsed AST.
///
/// Symbols do not exist in this stage.
pub struct Parse;

impl Stage for Parse {
    type Sym = String;
    type Pattern = ast::Pattern<Parse>;
    type Syms = ();
    type ExprData = ();
    type VarData = !;
    type BindingData = !;
}

/// Semantically resolved AST.
pub struct Sem;

impl Stage for Sem {
    type Sym = Symbol;
    type Pattern = ast::Pattern<Sem>;
    type Syms = Symbols<Sem>;
    type ExprData = ();
    type VarData = ();
    type BindingData = ();
}

/// Fully typed AST.
pub struct Typed;

impl Stage for Typed {
    type Sym = Symbol;
    type Pattern = patterns::PatternTree;
    type Syms = Symbols<Typed>;
    type ExprData = TypedExprData;
    type VarData = TypedVariableData;
    type BindingData = TypedBindingData;
}
