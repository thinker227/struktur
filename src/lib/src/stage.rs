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

use crate::{symbols::{Symbol, Symbols}, types::{TypedExprData, TypedFunctionData, TypedVariableData}, text_span::TextSpan};

/// The compilation stage of an AST.
pub trait Stage {
    /// Additional data for the root AST.
    type AstData: Debug + Clone;

    /// Additional data for nodes.
    type NodeData: Debug + Clone;

    /// Representation of symbols.
    type Sym: Debug + Clone;

    /// Global collection of symbols.
    type Syms: Debug;

    /// Additional data for expressions.
    type ExprData: Debug + Clone;

    /// Additional data for variables.
    type VarData: Debug + Clone;

    /// Additional data for functions.
    type FuncData: Debug + Clone;
}

/// Freshly parsed AST.
///
/// Symbols do not exist in this stage.
pub struct Parse;

impl Stage for Parse {
    type AstData = ();
    type NodeData = TextSpan;
    type Sym = String;
    type Syms = ();
    type ExprData = ();
    type VarData = !;
    type FuncData = !;
}

/// Semantically resolved AST.
pub struct Sem;

impl Stage for Sem {
    type AstData = ();
    type NodeData = TextSpan;
    type Sym = Symbol;
    type Syms = Symbols<Sem>;
    type ExprData = ();
    type VarData = ();
    type FuncData = ();
}

/// Fully typed AST.
pub struct Typed;

impl Stage for Typed {
    type AstData = ();
    type NodeData = TextSpan;
    type Sym = Symbol;
    type Syms = Symbols<Typed>;
    type ExprData = TypedExprData;
    type VarData = TypedVariableData;
    type FuncData = TypedFunctionData;
}
