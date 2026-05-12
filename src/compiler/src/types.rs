//! Definitions of Struktur types.

use std::rc::Rc;

use crate::{symbols::Symbol, text::TextLocation};

pub use meta_var::MetaVar;

mod check;
mod meta_var;

/// A type that is either a regular (mono-) type, or a type quantified over a set of type variables.
///
/// Only top-level bindings have a [PolyType] as their type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolyType {
    Forall(ForallType),
    Type(MonoType),
}

/// A regular non-quantified type.
///
/// This defines the type of expressions and variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MonoType {
    Primitive(Ty<PrimitiveType>),
    Function(Rc<Ty<FunctionType>>),
    Var(Ty<TypeVar>),
    Meta(MetaVar),
}

/// A primitive type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    Unit,
    Int,
    Bool,
    String,
}

/// The type of a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    /// The function's parameter/input type.
    pub param: Ty<MonoType>,
    /// The function's return/output type.
    pub ret: Ty<MonoType>,
}

/// A type quantified/generalized over a set of type variables.
///
/// *For all types t0...tn, the generalized type holds.*
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForallType {
    /// The type variables being quantified.
    pub vars: Vec<TypeVar>,
    /// The inner type being generalized over.
    pub generalized: Ty<MonoType>,
}

/// A type variable introduced by a [ForallType].
///
/// Not to be confused with [MetaVar]. [TypeVar] is a variable in the finalized typing of the program,
/// while [MetaVar] is a variable which only exists during type inference and which can be freely
/// substituted for other types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeVar {
    /// The type variable *symbol* the type is the *type* version of.
    ///
    /// I.e. this [TypeVar] is the *type* version of this type variable *[Symbol]*.
    pub symbol: Symbol,
}

/// A type with extra data attached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ty<T> {
    /// The type.
    pub ty: T,
    /// The type's provenance.
    pub provenance: Provenance,
}

/// The provenance of a type.
///
/// Provenance is a concept lifted from [*Getting into the Flow*](https://dl.acm.org/doi/10.1145/3622812)
/// which "explain *why* a certain type is used at a specific point in the program."
/// It's tracked during type inference and explains the flow of types
/// which led to a certain type—and possibly an error—being inferred.
///
/// A provenance just is a linear path through the constructions of types throughout the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Provenance {
    /// A specific point in the type flow of the program.
    Location(TextLocation),
    /// A path through several provenances.
    Path(Vec<Provenance>),
    /// The parameter type of a function.
    FunctionParam(Box<Provenance>),
    /// The return type of a function.
    FunctionRet(Box<Provenance>),
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
