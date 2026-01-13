//! Generic visitor pattern implementation.
//!
//! Largely inspired by the crate [derive_visitor](https://docs.rs/crate/derive-visitor).

use std::{any::Any, marker::PhantomData};

use crate::ast::AsNode;

/// Drives visitors through a type.
pub trait Drive: AsNode {
    /// Drives a visitor through the value.
    fn drive(&self, visitor: &mut dyn Visitor);
}

/// Types which can visit different types.
pub trait Visitor {
    /// Visits a value.
    fn visit(&mut self, item: &dyn Drive);

    fn visit_many<'a, T: Drive>(&mut self, items: impl IntoIterator<Item = &'a T>) where Self: Sized {
        for item in items {
            self.visit(item);
        }
    }
}

/// Supports visiting values of a specific type.
pub trait VisitT<T: Drive>: Visitor + Sized {
    /// Visits a value.
    fn visit_t(&mut self, item: &T);
}

impl<D: Drive> Drive for Vec<D> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        for item in self {
            visitor.visit(item);
        }
    }
}

impl<D: Drive> Drive for Option<D> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        if let Some(item) = self {
            visitor.visit(item);
        }
    }
}

impl Drive for () {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl Drive for ! {
    fn drive(&self, _: &mut dyn Visitor) {}
}

// Can be useful to have these unit implementations.

impl Visitor for () {
    #[inline]
    fn visit(&mut self, _: &dyn Drive) {}
}

impl<T: Drive> VisitT<T> for () {
    #[inline]
    fn visit_t(&mut self, _: &T) {}
}

trait Dispatch<V> {
    fn dispatch(visitor: &mut V, item: &dyn Drive);
}

pub struct Continue;

impl<V: Visitor> Dispatch<V> for Continue {
    #[inline]
    fn dispatch(visitor: &mut V, item: &dyn Drive) {
        item.drive(visitor);
    }
}

pub struct Dispatcher<V, T, N>(PhantomData<(V, T, N)>);

impl<V: VisitT<T>, T: Drive, N: Dispatch<V>> Dispatch<V> for Dispatcher<V, T, N> {
    #[inline]
    fn dispatch(visitor: &mut V, item: &dyn Drive) {
        if let Some(item) = (item as &dyn Any).downcast_ref::<T>() {
            visitor.visit_t(item);
        } else {
            N::dispatch(visitor, item);
        }
    }
}

/// Builds an implementation of a [Visitor].
// The entire purpose of this struct is to build up a big dispatcher type
// in the `D` parameter which can then be executed by passing it a visitor
// and a value to visit. In the base case, the `Continue` dispatcher is used
// which calls `Drive::drive` on the given type. Otherwise, `Dispatcher` is used
// to add a case for a type, and otherwise forwards to the 'next' dispatcher
// which is passed as the `N` type. None of this ever constructs a runtime value,
// so the final result is just a function which successively invokes several inlined
// dispatcher functions, creating barely any overhead.
#[derive(Debug, Clone, Copy)]
pub struct VisitorBuilder<V, D>(PhantomData<(V, D)>);

/// Creates a builder for a [Visitor] implementation.
/// Use [with](VisitorBuilder::with) to add types to the builder.
///
/// # Executing the visitor
/// When the visitor has been fully built, call [visit](VisitorBuilder::visit) to execute it.
/// If no builder for a given type has been added when executing the visitor,
/// the type's implementation of [drive](Drive::drive) will be called
/// so that visiting may continue.
#[inline]
pub const fn builder<V>() -> VisitorBuilder<V, Continue> {
    VisitorBuilder(PhantomData)
}

impl<V, D> VisitorBuilder<V, D> {
    /// Adds a type to the builder.
    #[inline]
    pub const fn with<T>(&self) -> VisitorBuilder<V, Dispatcher<V, T, D>>
    where
        T: Drive,
        V: VisitT<T>
    {
        VisitorBuilder(PhantomData)
    }
}

#[allow(private_bounds)]
impl<V: Visitor, D: Dispatch<V>> VisitorBuilder<V, D> {
    /// Visits a value with the types registered in the builder.
    #[inline]
    pub fn visit(self, visitor: &mut V, item: &dyn Drive) {
        D::dispatch(visitor, item);
    }
}

/// Creates an implementation of the [visit](Visitor::visit) method
/// which uses a set of types for which [VisitT] is implemented
/// by the current type.
#[macro_export]
macro_rules! visit {
    ($this:expr, $item:expr; $($t:ty),*) => {
        $crate::ast::visit::builder::<Self>()
        $( .with::<$t>() )*
            .visit($this, $item)
    };
}
