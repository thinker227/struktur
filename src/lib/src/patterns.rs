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
pub enum Occur {
    /// Match on the value of the target of the pattern matching.
    Identity,
}

/// An action executed by a row of patterns.
#[derive(Debug, Clone)]
pub struct Action {
    /// The index of the pattern case.
    /// Used to look up the expression to resolve the pattern to.
    pub case_index: usize,
}

/// A node in a compiled pattern decision tree.
#[derive(Debug, Clone)]
pub enum PatternTree {
    /// Match a pattern on an occurence and branch to a different node depending on the outcome.
    Match(Box<Match>),
    /// Perform a terminal action.
    Action(Action),
    /// Terminal failure of the entire pattern.
    Failure,
}

/// An application of a pattern onto an occurence.
#[derive(Debug, Clone)]
pub struct Match {
    /// The occurence to apply the pattern onto.
    occurence: Occur,
    /// The pattern to apply.
    pattern: Pat,
    /// The decision tree node to branch to in case the pattern succeds.
    success: PatternTree,
    /// The decision tree node to branch to in case the pattern fails.
    failure: PatternTree,
}

impl AsNode for PatternTree {}

impl Drive for PatternTree {
    fn drive(&self, _: &mut dyn Visitor) {}
}

/// Compiles a semantically resolved pattern into a decision tree.
pub fn compile_pattern(pattern: &ast::Pattern<Sem>) -> PatternTree {
    todo!()
}
