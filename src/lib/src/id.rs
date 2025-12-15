use std::{convert::identity, fmt::Debug, sync::{LazyLock, atomic::{AtomicUsize, Ordering}}};

/// Provides globally unique [Id]s and wraps them in a `T`.
///
/// `IdProvider` guarantees a couple things about the IDs it produces:
/// - IDs constructed by any provider are globally unique across the program
///   such that no two IDs returned by different calls to [`next`](Self::next) will ever be equal.
/// - IDs are produced in sequential order starting from 0.
pub struct IdProvider<T = Id> {
    unique: LazyLock<usize>,
    current: AtomicUsize,
    make: fn(Id) -> T,
}

impl<T> IdProvider<T> {
    /// Constructs a new provider by taking a function which wraps an [`Id`] produced by the provider.
    pub const fn new(make: fn(Id) -> T) -> Self {
        fn next_unique() -> usize {
            static UNIQUE: AtomicUsize = AtomicUsize::new(0);
            UNIQUE.fetch_add(1, Ordering::Relaxed)
        }

        Self {
            unique: LazyLock::new(next_unique),
            current: AtomicUsize::new(0),
            make
        }
    }

    /// Gets the next `T` using a new unique [`Id`].
    ///
    pub fn next(&self) -> T {
        let source = *self.unique;
        let shared = self.current.fetch_add(1, Ordering::Relaxed);
        let id = Id { source, shared };
        (self.make)(id)
    }
}

impl IdProvider<Id> {
    pub const fn new_plain() -> Self {
        Self::new(identity)
    }
}

impl<T> Debug for IdProvider<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IdProvider")
            .field("next_id", &self.current)
            .finish_non_exhaustive()
    }
}

/// A globally unique ID for the lifetime of the program (although not a UUID).
/// IDs are constructed exclusively by [`IdProvider`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id {
    source: usize,
    shared: usize,
}

impl From<Id> for usize {
    #[inline]
    fn from(value: Id) -> Self {
        value.shared
    }
}

impl Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Id").field(&self.shared).finish()
    }
}
