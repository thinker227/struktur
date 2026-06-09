use serde::Serialize;

use crate::syntax::NodeId;

/// The provenance of a type.
///
/// Provenance is a concept lifted from [*Getting into the Flow*](https://dl.acm.org/doi/10.1145/3622812)
/// which "explain *why* a certain type is used at a specific point in the program."
/// It's tracked during type inference and explains the flow of types
/// which led to a certain type—and possibly an error—being inferred.
///
/// A provenance just is a linear path through the constructions of types throughout the program.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Provenance {
    /// A path through several provenances.
    Path(Vec<Provenance>),
    /// Points to a type annotation.
    Annotation(NodeId),
    /// Points to a literal expression.
    Literal(NodeId),
    /// Points to the condition of an if-else expression.
    IfCondition(NodeId),
    /// Points to a lambda expression.
    Lambda(NodeId),
    /// Points to a function application expression.
    Application(NodeId),
    /// Points to a let binding that's been generalized.
    GeneralizeLet(NodeId),
    /// Points to a wildcard pattern (which, when part of a type-inferred pattern,
    /// potentially results in a generalization for which it is the provenance of).
    WildcardPattern(NodeId),
    /// Points to a variable pattern. Just like [WildcardPattern](Self::WildcardPattern),
    /// variable patterns can result in generalizations, so they have their own kind of provenance.
    VarPattern(NodeId),
    /// Points to a literal pattern.
    LiteralPattern(NodeId),
    /// The parameter type of a function.
    FunctionParam(Box<Provenance>),
    /// The return type of a function.
    FunctionRet(Box<Provenance>),
    /// A forall that's been generalized.
    Generalize { forall: Box<Provenance> },
    /// A variable introduced by a forall type that's been generalized.
    InferredVar { forall: Box<Provenance> },
}

impl Provenance {
    /// Joins two provenances together, forming a path.
    ///
    /// `other` is treated as coming *after* `self`.
    pub fn join(self, other: Self) -> Vec<Self> {
        match (self, other) {
            (Self::Path(mut a), Self::Path(b)) => {
                a.extend_from_slice(&b);
                a
            }
            (Self::Path(mut a), b) => {
                a.push(b);
                a
            }
            (a, Self::Path(mut b)) => {
                b.insert(0, a);
                b
            }
            (a, b) => vec![a, b],
        }
    }
}
