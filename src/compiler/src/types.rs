//! Definitions of Struktur types.

use crate::symbols::Symbol;

pub use check::type_check;
pub use meta_var::MetaVar;
pub use provenance::Provenance;
use serde::Serialize;

mod check;
mod meta_var;
pub mod pretty_print;
mod provenance;

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
/// Type variables may either be explicitly declared (i.e. through a `forall 'a. t` type annotation)
/// or inferred (i.e. by being a generalized unsolved unification variable).
///
/// Not to be confused with [MetaVar]. [TypeVar] is a variable in the finalized typing of the program,
/// while [MetaVar] is a variable which only exists during type inference and which can be freely
/// substituted for other types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum TypeVar {
    /// A variable introduced by an explicit type annotation.
    /// The [Symbol] is that assigned to a [VarTyExpr](crate::syntax::nodes::VarTyExpr).
    Declared(Symbol),
    /// A variable introduced by generalizing a let-binding and turning unsolved unification variables into type variables.
    /// The [usize] is an ID *unique per inference context*.
    Inferred(usize),
}

impl TypeVar {
    /// Gets the symbol of the variable, assuming it is declared.
    pub fn symbol(&self) -> Option<Symbol> {
        match self {
            TypeVar::Declared(symbol) => Some(*symbol),
            TypeVar::Inferred(_) => None,
        }
    }

    /// Gets the inference ID of the variable, assuming it is inferred.
    pub fn inference_id(&self) -> Option<usize> {
        match self {
            TypeVar::Declared(_) => None,
            TypeVar::Inferred(id) => Some(*id),
        }
    }
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
