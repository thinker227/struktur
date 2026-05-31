//! Definitions of Struktur types.

use crate::{symbols::Symbol, syntax::NodeId};

pub use check::type_check;
pub use meta_var::MetaVar;
use serde::Serialize;

mod check;
mod meta_var;

/// A type that is either a regular (mono-) type, or a type quantified over a set of type variables.
///
/// Only top-level bindings have a [PolyType] as their type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum PolyType {
    Forall(Ty<ForallType>),
    Type(MonoType),
}

/// A regular non-quantified type.
///
/// This defines the type of expressions and variables.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum MonoType {
    /// A primitive.
    Primitive(Ty<PrimitiveType>),
    /// A function.
    Function(Ty<Box<FunctionType>>),
    /// A type variable.
    Var(Ty<TypeVar>),
    /// A unification variable.
    /// This variant should *only* be present during unification.
    Meta(MetaVar),
}

/// A primitive type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum PrimitiveType {
    Unit,
    Int,
    Bool,
    String,
}

/// The type of a function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FunctionType {
    /// The function's parameter/input type.
    pub param: MonoType,
    /// The function's return/output type.
    pub ret: MonoType,
}

/// A type quantified/generalized over a set of type variables.
///
/// *For all types t0...tn, the generalized type holds.*
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ForallType {
    /// The type variables being quantified.
    pub vars: Vec<TypeVar>,
    /// The inner type being generalized over.
    pub generalized: MonoType,
}

/// A type variable introduced by a [ForallType].
///
/// Not to be confused with [MetaVar]. [TypeVar] is a variable in the finalized typing of the program,
/// while [MetaVar] is a variable which only exists during type inference and which can be freely
/// substituted for other types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct TypeVar {
    /// The type variable *symbol* the type is the *type* version of.
    ///
    /// I.e. this [TypeVar] is the *type* version of this type variable *[Symbol]*.
    pub symbol: Symbol,
}

impl From<Ty<PrimitiveType>> for MonoType {
    fn from(value: Ty<PrimitiveType>) -> Self {
        Self::Primitive(value)
    }
}

impl From<Ty<Box<FunctionType>>> for MonoType {
    fn from(value: Ty<Box<FunctionType>>) -> Self {
        Self::Function(value)
    }
}

impl From<Ty<TypeVar>> for MonoType {
    fn from(value: Ty<TypeVar>) -> Self {
        Self::Var(value)
    }
}

impl From<MetaVar> for MonoType {
    fn from(value: MetaVar) -> Self {
        Self::Meta(value)
    }
}

impl From<MonoType> for PolyType {
    fn from(value: MonoType) -> Self {
        Self::Type(value)
    }
}

impl From<Ty<ForallType>> for PolyType {
    fn from(value: Ty<ForallType>) -> Self {
        Self::Forall(value)
    }
}

/// A type with extra data attached.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Ty<T> {
    /// The type.
    pub ty: T,
    /// The type's provenance.
    pub provenance: Provenance,
}

impl<T> Ty<T> {
    /// Maps the type.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Ty<U> {
        Ty {
            ty: f(self.ty),
            provenance: self.provenance,
        }
    }

    pub fn with<U>(&self, ty: U) -> Ty<U> {
        Ty {
            ty,
            provenance: self.provenance.clone(),
        }
    }
}

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

/// Converts a number into a base-26 string using lowercase letters a-z.
///
/// Mainly used for displaying [TypeVar] and [MetaVar].
///
/// # Examples
/// ```
/// # use struktur::types::excel_column_name;
/// assert_eq!(&excel_column_name(0), "a");
/// assert_eq!(&excel_column_name(1), "b");
/// assert_eq!(&excel_column_name(2), "c");
/// // ...
/// assert_eq!(&excel_column_name(24), "y");
/// assert_eq!(&excel_column_name(25), "z");
/// assert_eq!(&excel_column_name(26), "aa");
/// assert_eq!(&excel_column_name(27), "ab");
/// // ...
/// assert_eq!(&excel_column_name(51), "az");
/// assert_eq!(&excel_column_name(52), "ba");
/// // ...
/// assert_eq!(&excel_column_name(700), "zy");
/// assert_eq!(&excel_column_name(701), "zz");
/// assert_eq!(&excel_column_name(702), "aaa");
/// assert_eq!(&excel_column_name(703), "aab");
/// ```
pub fn excel_column_name(mut index: usize) -> String {
    let mut result = String::new();
    index += 1;

    while index > 0 {
        let m = (index - 1) % 26;
        let c = char::from_u32('a' as u32 + m as u32).unwrap();
        result.insert(0, c);
        index = (index - m) / 26;
    }

    result
}
