//! Pattern decision trees.
//!
//! The algorithm used is largely based on
//! [How to compile pattern matching](https://julesjacobs.com/notes/patternmatching/patternmatching.pdf) by Jules Jacobs,
//! and [Yorick Peterse's implementation](https://github.com/yorickpeterse/pattern-matching-in-rust/blob/main/jacobs2021/src/lib.rs)
//! of it.

use std::collections::HashMap;

use crate::{ast::{self, AsNode, visit::{Drive, Visitor}}, stage::Sem, symbols::Symbol};

/// The target of a pattern (what Jacobs refers to as a "bound variable").
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Target {
    path: Vec<usize>,
}

impl Target {
    /// Returns an empty target which just traces to the input expression of a pattern.
    pub fn empty() -> Self {
        Self {
            path: vec![]
        }
    }

    /// Appends a new index to the target's path, returning a new [Target].
    pub fn append(&self, index: usize) -> Self {
        let mut path = self.path.clone();
        path.push(index);

        Self {
            path
        }
    }

    /// The 'path' traced through constructor arguments in order to reach the target.
    /// Each element is an index into a subsequent constructor's arguments.
    pub fn path(&self) -> &[usize] {
        &self.path
    }
}

/// A variable bound by a pattern.
#[derive(Debug, Clone)]
pub struct Binding {
    /// The variable symbol.
    pub variable: Symbol,
    /// The target which gives the value of the variable.
    pub value: Target,
}

/// The body of a clause or decision node.
#[derive(Debug, Clone)]
pub struct Body {
    /// The variables bound in the body.
    pub bindings: Vec<Binding>,
    /// The index of the action the body corresponds to.
    pub action: usize,
}

/// A match clause (or *row*).
#[derive(Debug, Clone)]
struct Clause {
    /// The patterns matched by the clause and the targets thereof,
    /// aka. the columns in the row.
    patterns: Vec<(Target, Pattern)>,
    /// The body of the clause.
    body: Body,
}

/// A data constructor.
#[derive(Debug, Clone, PartialEq)]
pub enum Constructor {
    /// Constructor of a boolean (true or false).
    Bool(bool),
    /// Constructor of a number (any of 2^64).
    Number(u64),
}

/// A pattern matched against a value.
#[derive(Debug, Clone, PartialEq)]
struct Pattern {
    /// The constructor the pattern is matching.
    constructor: Constructor,
    /// The arguments to the constructor.
    arguments: Vec<Pattern>,
}

/// A case matched against a target.
/// Equivalent to a [Pattern] but for decision nodes.
#[derive(Debug, Clone)]
pub struct Case {
    /// The constructor the case is matching.
    pub constructor: Constructor,
    pub body: Decision,
}

/// A node in a compiled pattern decision tree.
#[derive(Debug, Clone)]
pub enum Decision {
    /// Terminal success.
    Success(Body),
    /// Terminal failure of the entire pattern.
    Failure,
    /// Match a target against a set of cases.
    Match {
        /// The target to match.
        target: Target,
        /// The cases to match against.
        cases: Vec<Case>,
        /// The decision node to fall back on if no case matches.
        fallback: Option<Box<Decision>>,
    },
}

/// A collection of actions and a root decision tree node.
#[derive(Debug, Clone)]
pub struct Cases<T> {
    /// The root decision tree node.
    pub root: Decision,
    /// The actions referenced by the case indices in the decision tree.
    pub actions: Vec<T>,
}

/// Decides which target and pattern to branch on from a list of clauses.
fn branch(clauses: &[Clause]) -> &(Target, Pattern) {
    let mut counts = HashMap::new();

    for clause in clauses {
        for (target, _) in &clause.patterns {
            let entry = counts.entry(target).or_insert(0_usize);
            *entry += 1;
        }
    }

    clauses[0].patterns.iter()
        .max_by_key(|(target, _)| counts[target])
        .unwrap()
}

/// Expands a clause `a is C(P1, ..., Pn), ...REST` into `a1 is P1, ..., an is Pn, ...REST`,
/// with `a1, ..., an` being sub-targets of the passed-in target for each argument index in the constructor `C`.
///
/// If no pattern within the clause matches on the target, the original clause is returned unchanged.
fn expand(mut clause: Clause, target: &Target) -> Clause {
    let index = clause.patterns.iter()
        .enumerate()
        .find(|(_, (t, _))| t == target)
        .map(|(index, _)| index);

    if let Some(index) = index {
        let (_, pattern) = clause.patterns.remove(index);

        for (index, arg) in pattern.arguments.into_iter().enumerate() {
            clause.patterns.push((
                target.append(index),
                arg
            ));
        }
    }

    clause
}

/// Compiles a list of clauses into a decision tree.
fn compile_clauses(clauses: Vec<Clause>) -> Decision {
    // If there are no clauses, then we've reached a failure state.
    if clauses.is_empty() {
        return Decision::Failure;
    }

    // If the first clause is completely empty, then it is exhaustive and a success.
    if clauses.first().unwrap().patterns.is_empty() {
        let first = clauses.into_iter().next().unwrap();
        return Decision::Success(first.body);
    }

    let (branch_target, branch_pattern) = branch(&clauses).clone();

    let mut a = Vec::new();
    let mut b = Vec::new();

    for clause in clauses {
        // Check if the clause contains any test for the branch target.
        let overlap = clause.patterns.iter()
            .find(|(target, _)| *target == branch_target);

        if let Some((_, pattern)) = overlap {
            if pattern.constructor == branch_pattern.constructor {
                a.push(expand(clause, &branch_target));
            } else {
                b.push(clause);
            }
        } else {
            a.push(clause.clone());
            b.push(clause);
        }
    }

    let a = compile_clauses(a);
    let b = compile_clauses(b);

    Decision::Match {
        target: branch_target,
        cases: vec![Case {
            constructor: branch_pattern.constructor,
            // arguments:
            body: a
        }],
        fallback: Some(Box::new(b))
    }
}

/// Generates a [Clause] from an AST pattern node.
/// This conveniently also handles the operation of pushing variables to the right-hand side of patterns
/// as described in the algorithm, since we're modelling patterns in clauses
/// as unable to contain variable bindings.
fn generate_clause(pattern: &ast::Pattern<Sem>, index: usize) -> Clause {
    // TODO: This needs to take nested patterns into account once those are permitted.

    let (pattern, binding) = match pattern {
        // Unit patterns behave effectively the same as wildcards;
        // if they type-check, then they are irrefutable since the unit type
        // only has a single possible value.
        ast::Pattern::Wildcard(_) | ast::Pattern::Unit(_) => (None, None),

        ast::Pattern::Var(var) => (
            None,
            Some(Binding {
                variable: var.symbol,
                value: Target::empty()
            })
        ),

        ast::Pattern::Number(number) => (
            Some((
                Target::empty(),
                Pattern {
                    constructor: Constructor::Number(number.val),
                    arguments: vec![]
                }
            )),
            None
        ),

        ast::Pattern::Bool(bool) => (
            Some((
                Target::empty(),
                Pattern {
                    constructor: Constructor::Bool(bool.val),
                    arguments: vec![]
                }
            )),
            None
        ),
    };

    Clause {
        body: Body {
            bindings: binding.into_iter().collect(),
            action: index
        },
        patterns: pattern.into_iter().collect()
    }
}

/// Compiles a semantically resolved pattern into a decision tree.
pub fn compile_pattern(cases: &[&ast::Pattern<Sem>]) -> Decision {
    let clauses = cases.iter()
        .enumerate()
        .map(|(index, pattern)| generate_clause(pattern, index))
        .collect();

    compile_clauses(clauses)
}

impl AsNode for Decision {}

impl Drive for Decision {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<T: 'static> AsNode for Cases<T> {}

impl<T: 'static> Drive for Cases<T> {
    fn drive(&self, _: &mut dyn Visitor) {}
}
