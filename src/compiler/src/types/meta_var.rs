use std::{
    cell::OnceCell,
    fmt::{Debug, Display},
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use serde::Serialize;

use crate::types::excel_column_name;

use super::MonoType as Sub;

#[derive(Debug)]
struct Inner {
    ty: OnceCell<Sub>,
    level: AtomicU32,
    display_id: u32,
}

/// A type variable used during unification, more commonly referred to as a *unification variable*.
///
/// A unification variable can have one of two states; either it's unsubstituted—just being an opaque identifier,
/// or it's been substituted for another type. A unification variable can only ever be substituted for a single
/// type, and cannot be changed thereafter. Unification variables that have been substituted act completely
/// transparently, being entirely equivalent to their substitution.
///
/// Variables have a *level* associated with them which signifies at which level of function nesting it was introduced.
/// A variable's level can only ever be *lowered*, never raised.
/// This is used to properly allow eventual unsubsituted variables to be generalized into forall quantifiers.
///
/// Unification variables additionally contain a *display ID* represented as a number which is used to
/// distinguish variables from each other for display- and serialization purposes. While the implementation of [PartialEq]
/// does *not* rely on this ID, care should still be taken to ensure that the ID is unique among unification variables
/// that might be displayed or serialized as part of the same set of types (for instance in tests).
///
/// Unification variables utilize reference counting and interior mutability in order to allow
/// variables to be shared across multiple types while still refering to the same variable.
/// The [Clone] implementation for this type therefore just clones the reference and doesn't create a unique copy.
/// [inner_clone](Self::inner_clone) can be used to create a distinct copy of the variable.
///
/// Equality between variables is defined as two variables either being the same unsubstituted variable,
/// or being substituted for the same type. Note that equality takes into account the provenance of the substitued types.
#[derive(Clone)]
pub struct MetaVar(Rc<Inner>);

impl MetaVar {
    /// Creates a fresh unification variable.
    #[allow(clippy::new_without_default)]
    pub fn new(level: u32, display_id: u32) -> Self {
        Self(Rc::new(Inner {
            ty: OnceCell::new(),
            level: AtomicU32::new(level),
            display_id,
        }))
    }

    /// Gets the substitution of the variable, or [None] if the variable has not been substituted.
    pub fn get_sub(&self) -> Option<&Sub> {
        self.0.ty.get()
    }

    /// Gets the level of the variable.
    pub fn level(&self) -> u32 {
        self.0.level.load(Ordering::Relaxed)
    }

    /// Gets the display ID of the variable.
    pub fn display_id(&self) -> u32 {
        self.0.display_id
    }

    /// Tries to lower the level of the variable.
    ///
    /// If the new level is greater than or equal to the variable's current level,
    /// `false` is returned, otherwise `true`.
    pub fn try_lower_level(&self, new: u32) -> bool {
        if new < self.level() {
            self.0.level.store(new, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    /// Substitutes the variable for another type.
    ///
    /// Returns `false` if the type had already been substituted, otherwise `true`.
    pub fn sub(&self, ty: Sub) -> bool {
        self.0.ty.set(ty).is_ok()
    }

    /// Clones the variable by creating a fresh variable with the same level and substitution (if any),
    /// but which is a distinct variable.
    pub fn inner_clone(&self, display_id: u32) -> Self {
        Self(Rc::new(Inner {
            ty: self.0.ty.clone(),
            level: AtomicU32::new(self.level()),
            display_id,
        }))
    }
}

impl Display for MetaVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", excel_column_name(self.0.display_id as usize))
    }
}

impl Serialize for MetaVar {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if let Some(ty) = self.get_sub() {
            ty.serialize(serializer)
        } else {
            serializer.serialize_str(&self.to_string())
        }
    }
}

impl Debug for MetaVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MetaVar")
            .field("ty", &self.0.ty)
            .field("level", &self.0.level)
            .field("display_id", &self.0.display_id)
            .finish()
    }
}

impl PartialEq for MetaVar {
    fn eq(&self, other: &Self) -> bool {
        match (self.get_sub(), other.get_sub()) {
            (Some(a), Some(b)) => a == b,
            (None, None) => Rc::ptr_eq(&self.0, &other.0),
            _ => false,
        }
    }
}

impl Eq for MetaVar {}

impl PartialEq<Sub> for MetaVar {
    fn eq(&self, other: &Sub) -> bool {
        match self.get_sub() {
            Some(ty) => ty == other,
            None => false,
        }
    }
}
