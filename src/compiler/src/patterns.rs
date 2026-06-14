//! Compiled decision trees for pattern matching.
//!
//! The algorithm used is largely based on
//! [How to compile pattern matching](https://julesjacobs.com/notes/patternmatching/patternmatching.pdf) by Jules Jacobs,
//! and [Yorick Peterse's implementation](https://github.com/yorickpeterse/pattern-matching-in-rust/blob/main/jacobs2021/src/lib.rs)
//! of it.

use serde::{Serialize, ser::SerializeSeq as _};

use crate::{
    sources::SourceProject,
    symbols::{Symbol, Symbols},
    syntax::nodes,
};

/// The target a pattern is matched against (what Jacobs refers to as a "bound variable").
/// Represented as a path of indices into nested constructor arguments.
///
/// ```ignore
/// type List 'a = Nil | Cons { 'a, List }
///
/// let f = fun (List.Cons 1 (List.Cons 2 (List.Cons x List.Nil))) -> x
/// ```
/// In the above code, the path to `x` would be `[1, 1, 0]`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Target {
    path: Vec<usize>,
}

impl Target {
    /// Returns an empty target which just traces to the input expression of a pattern.
    pub fn empty() -> Self {
        Self { path: vec![] }
    }

    /// Pushes a new argument index to the target's path.
    pub fn push(&mut self, index: usize) {
        self.path.push(index);
    }

    /// Appends a new argument index to the target's path, returning a new [Target].
    ///
    /// If you have a `&mut Target`, use `push` instead which updates the target in-place.
    #[must_use]
    pub fn append(&self, index: usize) -> Self {
        let mut new = self.clone();
        new.push(index);
        new
    }

    /// Gets the length of the path.
    pub fn len(&self) -> usize {
        self.path.len()
    }

    /// Gets whether the path is empty.
    pub fn is_empty(&self) -> bool {
        self.path.is_empty()
    }

    /// The path traced through constructor arguments in order to reach the target.
    /// Each element is an index into a subsequent constructor's arguments.
    pub fn path(&self) -> &[usize] {
        &self.path
    }
}

impl Default for Target {
    fn default() -> Self {
        Self::empty()
    }
}

impl Serialize for Target {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;

        for index in &self.path {
            seq.serialize_element(index)?;
        }

        seq.end()
    }
}

/// A data constructor.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Constructor {
    /// Constructor of a boolean (true or false).
    Bool(bool),
    /// Constructor of a number (any of 2^64).
    Number(u64),
}

/// A variable bound by the body of a decision node.
#[derive(Debug, Clone, Serialize)]
pub struct Binding {
    /// The symbol of the variable that's bound.
    pub variable: Symbol,
    /// The target which gives the value of the variable.
    /// The path is absolute to the root expression.
    pub value: Target,
}

/// The body of a clause or decision node.
#[derive(Debug, Clone, Serialize)]
pub struct Body {
    /// The variables bound in the body.
    ///
    /// Instead of appearing as part of the pattern itself like they do in the AST,
    /// variables bound by a decision node are bound within the *body*.
    /// In effect, this can be conceptualized as one `let` expression per binding:
    /// ```ignore
    /// type Person = { String, Int }
    ///
    /// let f = fun (Person name age) -> ...
    /// // lowered into:
    /// let f = fun person -> let name = person.name in
    ///                       let age = person.age in
    ///                       ...
    /// ```
    pub bindings: Vec<Binding>,
    /// The index of the action the body performs.
    ///
    /// In lambdas, this will be the index of a case.
    /// In `let` expressions, this will always be 0 since `let` expressions don't branch.
    pub action: usize,
}

/// A match against a data constructor.
#[derive(Debug, Clone, Serialize)]
pub struct Case {
    /// The constructor matched against.
    pub constructor: Constructor,
    /// The decision node to branch to if the constructor matches.
    pub branch: Decision,
}

/// A node in a compiled decision tree of a pattern.
#[derive(Debug, Clone, Serialize)]
#[serde(untagged)]
pub enum Decision {
    /// A successful match.
    Success(Body),
    /// A failure to match the pattern (usually because the pattern is non-exhaustive).
    /// In most cases, this is an error.
    Failure,
    /// Match a sub-target against a set of cases,
    /// branching to one of the cases or a fallback.
    Match {
        /// The target of the match.
        /// The path is absolute to the root expression.
        target: Target,
        /// The cases to match the target against.
        cases: Vec<Case>,
        /// The decision node to fall back on if not case matches.
        fallback: Box<Decision>,
    },
}

/// A finalized decision tree.
///
/// This is mainly a convenience structure for grouping a root decision
/// node together with a list of actions referenced as indices by [Body]s in the tree.
#[derive(Debug, Clone, Serialize)]
pub struct DecisionTree<T> {
    /// The root node of the tree.
    pub root: Decision,
    /// The actions executed by [Body]s in the tree.
    pub actions: Vec<T>,
}

/// A match clause (or *row*).
///
/// When compiled, a [Decision] node is constructed from the clause
/// where the patterns end up as [Match](Decision::Match)es
/// and the body ends up as a leaf [Success](Decision::Success) node.
#[derive(Debug, Clone)]
struct Clause {
    /// The patterns matched by the clause and the targets thereof,
    /// aka. the columns in the row.
    _patterns: Vec<(Target, Pattern)>,
    /// The body of the clause.
    _body: Body,
}

/// A not yet compiled match against a data constructor,
/// effectively an intermediate representation of a [Case].
#[derive(Debug, Clone)]
struct Pattern {
    /// The constructor matched against.
    _constructor: Constructor,
    /// The patterns matched against the constructor arguments.
    _arguments: Vec<Pattern>,
}

/// A context for compiling patterns.
struct Context<'a> {
    symbols: &'a Symbols,
    sources: &'a SourceProject,
}

/// Generates a [Clause] from an AST pattern node.
/// This conveniently also handles the operation of pushing variables to the right-hand side of patterns
/// as described in the algorithm, since we're modelling patterns in clauses
/// as unable to contain variable bindings.
fn generate_clause(ctx: &Context, pattern: nodes::Pattern, action: usize) -> Clause {
    let (pattern, binding) = match pattern {
        nodes::Pattern::Wildcard(_) | nodes::Pattern::Unit(_) => (None, None),

        nodes::Pattern::Var(var) => (
            None,
            Some(Binding {
                variable: ctx.symbols.bound(var).unwrap().key(),
                value: Target::empty(),
            }),
        ),

        nodes::Pattern::Number(number) => (
            Some((
                Target::empty(),
                Pattern {
                    _constructor: Constructor::Number(
                        ctx.sources
                            .lookup(number.location())
                            .unwrap()
                            .parse::<u64>()
                            .expect("unexpected number literal text"),
                    ),
                    _arguments: vec![],
                },
            )),
            None,
        ),

        nodes::Pattern::Bool(bool) => (
            Some((
                Target::empty(),
                Pattern {
                    _constructor: Constructor::Bool(
                        ctx.sources
                            .lookup(bool.location())
                            .unwrap()
                            .parse::<bool>()
                            .expect("unexpected bool literal text"),
                    ),
                    _arguments: vec![],
                },
            )),
            None,
        ),

        nodes::Pattern::TyAnn(ann) => {
            return generate_clause(ctx, ann.pattern(), action);
        }

        nodes::Pattern::Grouping(grouping) => {
            return generate_clause(ctx, grouping.pattern(), action);
        }
    };

    Clause {
        _body: Body {
            bindings: binding.into_iter().collect(),
            action,
        },
        _patterns: pattern.into_iter().collect(),
    }
}

/// Decides which target and pattern to branch on from a list of clauses.
fn _branch(_clauses: &[Clause]) -> &(Target, Pattern) {
    todo!()
}

/// Expands a clause `a is C(P1, ..., Pn), ...REST` into `a1 is P1, ..., an is Pn, ...REST`,
/// with `a1, ..., an` being sub-targets of the passed-in target for each argument index in the constructor `C`.
///
/// If no pattern within the clause matches on the target, the original clause is returned unchanged.
fn _expand(_clause: Clause, _target: &Target) -> Clause {
    todo!()
}

/// Compiles a set of clauses into a decision tree.
fn compile_clauses(_clauses: &[Clause]) -> Decision {
    todo!()
}

/// Compiles a set of patterns into a decision tree.
pub fn compile_pattern<'map>(
    cases: impl Iterator<Item = nodes::Pattern<'map>>,
    sources: &SourceProject,
    symbols: &Symbols,
) -> Decision {
    let ctx = Context { sources, symbols };

    let clauses = cases
        .enumerate()
        .map(|(index, pattern)| generate_clause(&ctx, pattern, index))
        .collect::<Vec<_>>();

    compile_clauses(&clauses)
}
