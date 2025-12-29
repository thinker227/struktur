use std::{fmt::Debug, sync::{Arc, OnceLock, atomic::{AtomicUsize, Ordering}}};

use crate::{id::Id, types::inference::InferType};

/// A type variable used for unification.
#[derive(Clone)]
pub struct MetaVar(Arc<Inner>);

struct Inner {
    id: Id,
    // Nothing in the compiler is multi-threaded, but we have to guarantee that type-related stuff is Send+Sync
    // because Miette requires that diagnostics are, and we want to be able to store types in diagnostics.
    level: AtomicUsize,
    sub: OnceLock<InferType>,
}

impl MetaVar {
    /// Creates a new variable.
    pub fn new(id: Id, level: usize) -> Self {
        Self(Arc::new(Inner {
            id,
            level: AtomicUsize::new(level),
            sub: OnceLock::new()
        }))
    }

    /// Gets the level of the variable.
    pub fn level(&self) -> usize {
        // Not sure if relaxed is technically the right ordering here,
        // but we're not actually multi-threaded so it doesn't matter.
        self.0.level.load(Ordering::Relaxed)
    }

    /// Attempts to lower the level of the variable.
    ///
    /// A variable's level is only allowed to be *lowered*,
    /// so if the level is attempted to be *raised* then this function returns `Err`.
    pub fn try_lower_level(&self, new: usize) -> Result<(), ()> {
        if new < self.level() {
            // Not sure if relaxed is technically the right ordering here,
            // but we're not actually multi-threaded so it doesn't matter.
            self.0.level.store(new, Ordering::Relaxed);
            Ok(())
        } else {
            Err(())
        }
    }

    /// Substitutes the variable for another type.
    /// Can only be done once per variable.
    pub fn sub(&self, ty: InferType) -> Result<(), InferType> {
        self.0.sub.set(ty)
    }

    /// Gets the substitution of the variable.
    pub fn get_sub(&self) -> Option<&InferType> {
        self.0.sub.get()
    }
}

impl PartialEq for MetaVar {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}

impl Debug for MetaVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.get_sub() {
            Some(sub) => f.debug_struct("MetaVar")
                .field("id", &self.0.id)
                .field("level", &self.level())
                .field("sub", sub)
                .finish(),
            None => f.debug_struct("MetaVar")
                .field("id", &self.0.id)
                .field("level", &self.level())
                .finish_non_exhaustive()
        }
    }
}
