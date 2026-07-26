// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cell types for verified interior mutability.
//!
//! These are specification-level cell types matching Creusot's `cell` module.
//! They provide verified interior mutability with ghost permissions.
//!
//! Source: Creusot `creusot-std/src/cell.rs`

use core::{
    borrow::{Borrow, BorrowMut},
    cell::{Cell, UnsafeCell},
    hash::{Hash, Hasher},
    ptr,
};

use crate::{
    ghost::{perm::Perm, Ghost, Snapshot},
    logic::{unreachable, Mapping, View},
};

/// A `Cell<T>` with a predicate-based invariant.
///
/// In Creusot, `PredCell<T>` wraps a `Cell<T>` and carries a ghost predicate
/// describing valid values. The predicate is verifier-only; runtime behavior
/// matches `core::cell::Cell`.
#[repr(transparent)]
pub struct PredCell<T: ?Sized>(Cell<T>);

impl<T> View for PredCell<T> {
    type ViewTy = Mapping<T, bool>;

    fn view(self) -> Self::ViewTy {
        unreachable()
    }
}

impl<T> PredCell<T> {
    /// Create a new `PredCell` with the given initial value.
    pub fn new<P>(value: T, _pred: Snapshot<P>) -> Self {
        Self(Cell::new(value))
    }

    /// Set a new value.
    pub fn set(&self, value: T) {
        self.0.set(value);
    }

    /// Swap values with another cell.
    pub fn swap(&self, other: &PredCell<T>) {
        self.0.swap(&other.0);
    }

    /// Replace the contained value with a new one, returning the old value.
    pub fn replace(&self, value: T) -> T {
        self.0.replace(value)
    }

    /// Consume the cell and return the inner value.
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: Copy> PredCell<T> {
    /// Get the current value.
    pub fn get(&self) -> T {
        self.0.get()
    }

    /// Update the current value.
    pub fn update(&self, f: impl FnOnce(T) -> T) {
        self.0.update(f);
    }
}

impl<T: ?Sized> PredCell<T> {
    /// Build a `PredCell` reference from a mutable reference.
    pub fn from_mut<P>(t: &mut T, _pred: Snapshot<P>) -> &PredCell<T> {
        // SAFETY: `PredCell<T>` is `repr(transparent)` over `Cell<T>`.
        unsafe { &*(core::ptr::from_ref(Cell::from_mut(t)) as *const PredCell<T>) }
    }
}

impl<T: Default> PredCell<T> {
    /// Take the current value, replacing with `Default::default()`.
    pub fn take(&self) -> T {
        self.0.take()
    }
}

impl<T> PredCell<[T]> {
    /// Convert to a slice of `PredCell<T>`, matching `Cell::as_slice_of_cells`.
    pub fn as_slice_of_cells<P>(&self, _pred: Snapshot<P>) -> &[PredCell<T>] {
        // SAFETY: `PredCell<T>` is `repr(transparent)` over `Cell<T>`.
        unsafe { &*(core::ptr::from_ref(self.0.as_slice_of_cells()) as *const [PredCell<T>]) }
    }
}

/// A `Cell<T>` with permission-based ghost ownership.
///
/// In Creusot, `PermCell<T>` is a cell whose access is governed by a
/// ghost permission token (`Perm`). Reading or writing requires holding
/// the permission.
#[repr(transparent)]
pub struct PermCell<T: ?Sized>(UnsafeCell<T>);

impl<T> View for PermCell<T> {
    type ViewTy = T;

    fn view(self) -> Self::ViewTy {
        unreachable()
    }
}

impl<T> Clone for PermCell<T> {
    fn clone(&self) -> Self {
        panic!("PermCell::clone called at runtime - only valid in ghost code")
    }
}

impl<T> PermCell<T> {
    /// Create a new `PermCell` with the given initial value.
    ///
    /// Returns a tuple of the cell and a ghost permission token, matching
    /// Creusot's `PermCell::new` signature exactly:
    /// `fn new(value: T) -> (Self, Ghost<Box<Perm<PermCell<T>>>>)`.
    ///
    /// The permission is boxed (`Ghost<Box<Perm<_>>>`) so that downstream
    /// idioms such as `ghost!(&**own)` / `ghost!(&mut **own)` chain through
    /// `Ghost → Box → Perm` correctly. `borrow`/`borrow_mut`/`replace`/`set`
    /// accept any type that `Borrow`s `Perm<PermCell<T>>`, so callers holding
    /// either `Ghost<&Box<Perm<_>>>` or `Ghost<&Perm<_>>` keep working.
    ///
    /// Reference: Creusot `creusot-std/src/cell/permcell.rs:58`.
    pub fn new(value: T) -> (Self, Ghost<Box<Perm<PermCell<T>>>>) {
        let cell = Self(UnsafeCell::new(value));
        let perm = Ghost::conjure();
        (cell, perm)
    }

    /// Set a new value (requires permission).
    ///
    /// # Safety
    ///
    /// Requires exclusive permission for the cell.
    pub unsafe fn set(&self, _perm: Ghost<&mut Perm<PermCell<T>>>, value: T) {
        unsafe {
            *self.0.get() = value;
        }
    }

    /// Replace the contained value with a new one, returning the old value.
    ///
    /// # Safety
    ///
    /// Requires exclusive permission for the cell.
    pub unsafe fn replace(&self, _perm: Ghost<&mut Perm<PermCell<T>>>, value: T) -> T {
        unsafe { core::ptr::replace(self.0.get(), value) }
    }

    /// Consume the cell and return the inner value.
    ///
    /// Takes ownership of the permission token. Matches Creusot's
    /// `into_inner(self, perm: Ghost<Box<Perm<PermCell<T>>>>) -> T`. Accepts
    /// both `Ghost<Perm<_>>` and `Ghost<Box<Perm<_>>>` through the generic
    /// permission parameter so callers holding either shape compile.
    pub fn into_inner<P: Borrow<Perm<PermCell<T>>>>(self, _perm: Ghost<P>) -> T {
        self.0.into_inner()
    }

    /// Borrow the cell's value immutably (requires permission).
    ///
    /// # Safety
    ///
    /// Requires that no mutable borrow to the inner value exists.
    /// In verified code, this is enforced by the ghost permission system.
    pub unsafe fn borrow<'a, P>(&'a self, _perm: Ghost<&'a P>) -> &'a T
    where
        P: Borrow<Perm<PermCell<T>>> + ?Sized,
    {
        unsafe { &*self.0.get() }
    }

    /// Borrow the cell's value mutably (requires permission).
    ///
    /// # Safety
    ///
    /// Requires that no other borrow to the inner value exists.
    /// In verified code, this is enforced by the ghost permission system.
    #[allow(clippy::mut_from_ref)] // Interior mutability: permission ghost token ensures exclusivity.
    pub unsafe fn borrow_mut<'a, P>(&'a self, _perm: Ghost<&'a mut P>) -> &'a mut T
    where
        P: BorrowMut<Perm<PermCell<T>>> + ?Sized,
    {
        unsafe { &mut *self.0.get() }
    }
}

impl<T: Copy> PermCell<T> {
    /// Get the current value (requires permission, `T: Copy`).
    ///
    /// Accepts both `Ghost<&Perm<PermCell<T>>>` and `Ghost<&Box<Perm<PermCell<T>>>>`
    /// via the `Borrow` bound. In Creusot ghost blocks, unwrapping
    /// `Option<Box<Perm<...>>>` produces `&Box<Perm<...>>` which needs to be
    /// compatible with this method's signature.
    ///
    /// # Safety
    ///
    /// Requires shared permission for the cell.
    pub unsafe fn get<P: std::borrow::Borrow<Perm<PermCell<T>>>>(&self, _perm: Ghost<&P>) -> T {
        unsafe { *self.0.get() }
    }
}

impl<T> PermCell<T> {
    /// Returns a raw pointer to the underlying data.
    pub fn as_ptr(&self) -> *mut T {
        self.0.get()
    }

    /// Build a `PermCell` reference from a mutable reference.
    pub fn from_mut(t: &mut T) -> (&PermCell<T>, Ghost<&mut Perm<PermCell<T>>>) {
        // SAFETY: `PermCell<T>` is `repr(transparent)` over `T`.
        let cell: &PermCell<T> = unsafe { &*core::ptr::from_mut(t).cast::<PermCell<T>>() };
        (cell, Ghost::conjure())
    }
}

impl<T: Default> PermCell<T> {
    /// Take the current value, replacing with `Default::default()`.
    ///
    /// # Safety
    ///
    /// Requires exclusive permission for the cell.
    pub unsafe fn take(&self, perm: Ghost<&mut Perm<PermCell<T>>>) -> T {
        unsafe { self.replace(perm, T::default()) }
    }
}

// ── Creusot parity: Container, Send/Sync ─────────────────────────────

impl<T: Sized> crate::ghost::perm::Container for PermCell<T> {
    type Value = T;

    fn is_disjoint(&self, _self_val: &T, other: &Self, _other_val: &T) -> bool {
        // Identity-based disjointness: two distinct PermCells are disjoint.
        // In verification, this is a logical predicate (self != other).
        // At runtime, we use pointer identity.
        !core::ptr::eq(self, other)
    }
}

// SAFETY: `PermCell<T>` wraps `UnsafeCell<T>` with ghost permission tracking.
// The permission system ensures exclusive access, making cross-thread use safe
// when the verifier confirms permission discipline.
// Matches Creusot: `unsafe impl<T> Send for PermCell<T> {}`
unsafe impl<T> Send for PermCell<T> {}
// Matches Creusot: `unsafe impl<T> Sync for PermCell<T> {}`
unsafe impl<T> Sync for PermCell<T> {}

// SAFETY: `Perm<PermCell<T>>` is a ghost (zero-sized) token. It carries no
// runtime data and cannot create data races.
// Matches Creusot: `unsafe impl<T: Send> Send for Perm<PermCell<T>> {}`
unsafe impl<T: Send> Send for Perm<PermCell<T>> {}
// Matches Creusot: `unsafe impl<T: Sync> Sync for Perm<PermCell<T>> {}`
unsafe impl<T: Sync> Sync for Perm<PermCell<T>> {}

/// Built-in contracts for cell wrappers used by `trust-wp-driver`.
#[doc(hidden)]
pub mod specs {
    /// Contract for `PredCell::new`.
    pub const PREDCELL_NEW: &str = r"
        params: value, _pred
        requires: _pred[value]
        ensures: result@ == *_pred
    ";

    /// Contract for `PredCell::get`.
    pub const PREDCELL_GET: &str = r"
        params: self
        ensures: self@[result]
    ";

    /// Contract for `PredCell::set`.
    pub const PREDCELL_SET: &str = r"
        params: self, value
        requires: self@[value]
    ";

    /// Contract for `PredCell::swap`.
    ///
    /// Both cells must share the same predicate. Creusot requires
    /// `forall<x: T> self@[x] == other@[x]`.
    pub const PREDCELL_SWAP: &str = r"
        params: self, other
        requires: forall<x: _> self@[x] == other@[x]
    ";

    /// Contract for `PredCell::replace`.
    pub const PREDCELL_REPLACE: &str = r"
        params: self, value
        requires: self@[value]
        ensures: self@[result]
    ";

    /// Contract for `PredCell::into_inner`.
    pub const PREDCELL_INTO_INNER: &str = r"
        params: self
        ensures: self@[result]
    ";

    /// Contract for `PredCell::update`.
    ///
    /// The closure must preserve the predicate: if `self@[x]`, then after
    /// calling `f(x)`, the result must also satisfy `self@[result]`.
    ///
    /// Matches Creusot: two requires + one ensures witnessing the update.
    /// Reference: creusot-std/src/cell/predcell.rs:71-74
    pub const PREDCELL_UPDATE: &str = r"
        params: self, f
        requires: forall<x: _> self@[x] ==> f.precondition((x,))
        requires: forall<x: _, res: _> self@[x] && f.postcondition_once((x,), res) ==> self@[res]
        ensures: exists<x: _, res: _> self@[x] && f.postcondition_once((x,), res)
    ";

    /// Contract for `PredCell::from_mut`.
    pub const PREDCELL_FROM_MUT: &str = r"
        params: t, _pred
        requires: _pred[*t]
        ensures: _pred[^t]
        ensures: result@ == *_pred
    ";

    /// Contract for `PredCell::take`.
    pub const PREDCELL_TAKE: &str = r"
        params: self
        requires: forall<x: _> core::default::Default::default.postcondition((), x) ==> self@[x]
        ensures: self@[result]
    ";

    /// Contract for `PredCell::as_slice_of_cells`.
    pub const PREDCELL_AS_SLICE_OF_CELLS: &str = r"
        params: self, _pred
        ensures: result@.len() == _pred.len()
        ensures: forall<i: Int> 0 <= i && i < _pred.len() ==> result[i]@ == _pred[i]
        ensures: forall<i: Int, x: _> 0 <= i && i < _pred.len() ==> result[i]@[x] == _pred[i][x]
    ";

    /// Contract for `PermCell::new`.
    pub const PERMCELL_NEW: &str = r"
        params: value
        ensures: result.0@ == value
    ";

    /// Contract for `PermCell::set`.
    pub const PERMCELL_SET: &str = r"
        params: self, _perm, value
        ensures: (^self)@ == value
    ";

    /// Contract for `PermCell::get`.
    pub const PERMCELL_GET: &str = r"
        params: self, _perm
        ensures: result == self@
    ";

    /// Contract for `PermCell::borrow`.
    pub const PERMCELL_BORROW: &str = r"
        params: self, _perm
        ensures: *result == self@
    ";

    /// Contract for `PermCell::borrow_mut`.
    pub const PERMCELL_BORROW_MUT: &str = r"
        params: self, _perm
        ensures: *result == self@
        ensures: ^result == (^self)@
    ";

    /// Contract for `PermCell::replace`.
    pub const PERMCELL_REPLACE: &str = r"
        params: self, _perm, value
        ensures: result == self@
        ensures: (^self)@ == value
    ";

    /// Contract for `PermCell::into_inner`.
    pub const PERMCELL_INTO_INNER: &str = r"
        params: self, _perm
        ensures: result == self@
    ";

    /// Contract for `PermCell::from_mut`.
    pub const PERMCELL_FROM_MUT: &str = r"
        params: t
        ensures: result.0@ == *t
        ensures: (^result.0)@ == ^t
    ";

    /// Contract for `PermCell::take`.
    pub const PERMCELL_TAKE: &str = r"
        params: self, _perm
        ensures: result == self@
        ensures: core::default::Default::default.postcondition((), (^self)@)
    ";

    /// Contract for `PermCell::as_ptr`.
    ///
    /// Creusot uses `#[ensures(true)]` — the pointer is opaque at the spec level.
    /// This prevents the call from being classified as opaque.
    pub const PERMCELL_AS_PTR: &str = "";
}

impl<T: ?Sized> PartialEq for PermCell<T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl<T: ?Sized> Eq for PermCell<T> {}

/// Pointer-identity-based hashing for `PermCell<T>`.
///
/// `PermCell` values are compared by pointer identity (see `PartialEq` impl).
/// Hashing follows the same semantics: two `PermCell` references hash equally
/// iff they point to the same allocation. This is required for `PermCell` to
/// be usable as a key in `FMap`, which backs ghost ownership maps in concurrent
/// verification examples (e.g., `persistent_array.rs`).
impl<T: ?Sized> Hash for PermCell<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        ptr::from_ref(self).hash(state);
    }
}
