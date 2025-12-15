use std::{cell::{Cell, OnceCell}, fmt::Debug, rc::Rc};

use crate::{id::Id, types::inference::InferType};

/// A type variable used for unification.
#[derive(Clone)]
pub struct MetaVar(Rc<Inner>);

struct Inner {
    id: Id,
    level: Cell<usize>,
    sub: OnceCell<InferType>,
}

impl MetaVar {
    /// Creates a new variable.
    pub fn new(id: Id, level: usize) -> Self {
        Self(Rc::new(Inner {
            id,
            level: Cell::new(level),
            sub: OnceCell::new()
        }))
    }

    /// Gets the level of the variable.
    pub fn level(&self) -> usize {
        self.0.level.get()
    }

    /// Attempts to lower the level of the variable.
    ///
    /// A variable's level is only allowed to be *lowered*,
    /// so if the level is attempted to be *raised* then this function returns `Err`.
    pub fn try_lower_level(&self, new: usize) -> Result<(), ()> {
        if new < self.level() {
            self.0.level.set(new);
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
                .field("level", &self.0.level.get())
                .field("sub", sub)
                .finish(),
            None => f.debug_struct("MetaVar")
                .field("id", &self.0.id)
                .field("level", &self.0.level.get())
                .finish_non_exhaustive()
        }
    }
}
