//! Pattern decision trees.
//!
//! The algorithm used is largely based on
//! [Compiling Pattern Matching](https://compiler.club/compiling-pattern-matching/)
//! by Colin James.

use crate::{ast::{self, AsNode, visit::{Drive, Visitor}}, stage::Sem, symbols::Symbol};

mod matrix;

/// A pattern.
#[derive(Debug, Clone)]
pub enum Pat {
    /// Matches a specific number.
    Number(u64),
    /// Matches a boolean.
    Bool(bool),
    /// A pattern which will always match.
    Wildcard(Wildcard),
}

/// A pattern which will always match and might additionally bind a variable.
/// Additionally includes unit patterns, since unit patterns are irrefutable.
#[derive(Debug, Clone)]
pub struct Wildcard {
    /// The variable bound by the pattern.
    pub var: Option<Symbol>,
}

/// Describes a sequence of operations required to get to the value
/// being matched on by a column of patterns.
#[derive(Debug, Clone)]
pub struct Occur;

/// An action executed by a row of patterns.
#[derive(Debug, Clone)]
pub struct Action;

/// A compiled pattern decision tree.
#[derive(Debug, Clone)]
pub struct PatternTree {

}

impl AsNode for PatternTree {}

impl Drive for PatternTree {
    fn drive(&self, _: &mut dyn Visitor) {}
}

/// Compiles a semantically resolved pattern into a decision tree.
pub fn compile_pattern(pattern: &ast::Pattern<Sem>) -> PatternTree {
    todo!()
}
