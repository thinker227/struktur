//! Types and type-checking.

#![allow(private_interfaces)]

mod inference;
pub mod pretty_print;

use std::{fmt::Debug, sync::Arc};
use derivative::Derivative;

use crate::{id::Id, symbols::Symbol, types::pretty_print::PrettyPrint};

pub use self::inference::{TypeCheckError, type_check};

/// The representation of a type.
///
/// Equivalent to [`Stage`](crate::stage::Stage) but for types
/// in order to type-safely represent type variables or the absence thereof.
///
/// Note that type variables are not exposed outside this module
/// and the only exposed implementor of this trait is [`Pruned`].
pub trait Repr {
    /// Recursive types within other types.
    ///
    /// [`MonoType`] is, as the name implies, any type except a type variable,
    /// but types nested within a [`MonoType`] (like function parameters or return types)
    /// might still be or contain type variables,
    /// so this specifies the Rust type for these recursive types.
    type RecTy: Clone + Debug + PartialEq + PrettyPrint;
    // type RecTy: Clone + Debug + PartialEq + Instantiate;
}

/// Types that are pruned and do not contain type variables.
pub struct Pruned;

impl Repr for Pruned {
    type RecTy = MonoType<Pruned>;
}

/// A type in the type system.
pub type Type = MonoType<Pruned>;

/// A type which is not generalized over.
///
/// This is more elegantly exposed as the alias [`Type`].
///
/// Much in the same way as the AST, types are parameterized by a "representation"
/// in order to type-safely deal with unification variables which may or may not be present,
/// although the only representation publicly exposed is [`Pruned`] since only this
/// module ever has to worry about unification variables.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""), PartialEq(bound = ""))]
pub enum MonoType<R: Repr = Pruned> {
    /// A primitive type.
    Primitive(Primitive),
    /// A function from one type to another.
    Function(Arc<FunctionType<R>>),
    /// A type variable introduced by a [`Forall`] generalization, aka. a type parameter.
    Var(TypeVar),
}

/// A primitive type which makes up the leaves of a type "tree".
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Primitive {
    /// The unit single-value type.
    Unit,
    /// 64-bit integers.
    Int,
    /// Booleans.
    Bool,
    /// Strings.
    String,
}

/// The type of a function.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""), PartialEq(bound = ""))]
pub struct FunctionType<R: Repr> {
    pub param: R::RecTy,
    pub ret: R::RecTy,
}

/// A type which may be a [`Forall`] generalization.
#[derive(Debug, Clone, PartialEq)]
pub enum PolyType<Ty> {
    Forall(Forall<Ty>),
    Type(Ty),
}

/// A generalization of a type over one or more type variables.
#[derive(Debug, Clone, PartialEq)]
pub struct Forall<Ty> {
    vars: Vec<TypeVar>,
    target: Ty,
}

/// A type variable introducted by a [`Forall`] generalization, aka. a type parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar {
    id: Id,
    declaring_symbol: Option<Symbol>,
}

impl<R: Repr> MonoType<R> {
    /// The unit single-value type.
    pub fn unit() -> Self {
        Self::Primitive(Primitive::Unit)
    }

    /// 64-bit integers.
    pub fn int() -> Self {
        Self::Primitive(Primitive::Int)
    }

    /// Booleans.
    pub fn bool() -> Self {
        Self::Primitive(Primitive::Bool)
    }

    /// Strings.
    pub fn string() -> Self {
        Self::Primitive(Primitive::String)
    }

    /// A function from one type to another.
    pub fn function(param: R::RecTy, ret: R::RecTy) -> Self {
        Self::Function(Arc::new(FunctionType {
            param,
            ret
        }))
    }
}

impl<Ty> PolyType<Ty> {
    /// Maps the type within the polytype,
    /// either the target type of the [`Forall`], or the raw type.
    pub fn map<Other>(self, f: impl FnOnce(Ty) -> Other) -> PolyType<Other> {
        match self {
            PolyType::Forall(forall) => PolyType::Forall(Forall {
                vars: forall.vars,
                target: f(forall.target)
            }),
            PolyType::Type(ty) => PolyType::Type(f(ty)),
        }
    }

    /// Gets a reference to the inner type of the polytype,
    /// either the plain type of the type generalized over in a forall.
    pub fn inner(&self) -> &Ty {
        match self {
            PolyType::Forall(forall) => &forall.target,
            PolyType::Type(ty) => ty
        }
    }
}

impl<Ty> Forall<Ty> {
    /// Maps the type within the forall.
    pub fn map<Other>(self, f: impl FnOnce(Ty) -> Other) -> Forall<Other> {
        Forall {
            target: f(self.target),
            vars: self.vars
        }
    }
}

impl<R: Repr> From<Primitive> for MonoType<R> {
    fn from(value: Primitive) -> Self {
        Self::Primitive(value)
    }
}

impl<R: Repr> From<FunctionType<R>> for MonoType<R> {
    fn from(value: FunctionType<R>) -> Self {
        Self::Function(Arc::new(value))
    }
}

impl<Ty> From<Forall<Ty>> for PolyType<Ty> {
    fn from(value: Forall<Ty>) -> Self {
        PolyType::Forall(value)
    }
}

/// Additional data for typed expressions.
#[derive(Debug, Clone)]
pub struct TypedExprData {
    pub ty: MonoType<Pruned>,
}

/// Additional data for typed variables.
#[derive(Debug, Clone)]
pub struct TypedVariableData {
    pub ty: PolyType<MonoType<Pruned>>,
}

/// Additional data for typed functions.
#[derive(Debug, Clone)]
pub struct TypedBindingData {
    pub ty: PolyType<MonoType<Pruned>>,
}
