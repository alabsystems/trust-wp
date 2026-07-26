// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sync view types for atomic invariant protocols.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! In Creusot, `SyncView` represents a thread's view of shared memory for
//! reasoning about release-acquire and sequentially-consistent atomic
//! operations. `Timestamp` is used to track ordering between views.
//!
//! This module provides stub types for compilation compatibility with Creusot
//! tests that use atomic invariants.
//!
//! Reference: Creusot `creusot-std/src/sync_view.rs`

use core::marker::PhantomData;

use crate::{ghost::Ghost, logic::Int, trusted};

/// A timestamp for ordering atomic operations.
///
/// In Creusot, timestamps are integers used to track the causal ordering
/// of atomic load/store operations within a sync view.
///
/// Reference: Creusot `creusot-std/src/sync_view.rs:28`
pub type Timestamp = Int;

/// Trait for types that can produce timestamps from sync views.
///
/// Reference: Creusot `creusot-std/src/sync_view.rs:30-38`
pub trait HasTimestamp {
    /// Get the timestamp for this value at a given sync view.
    ///
    /// Ghost-only — panics at runtime.
    #[trusted]
    fn get_timestamp(self, _view: SyncView) -> Timestamp
    where
        Self: Sized,
    {
        panic!("ghost code only")
    }

    /// Monotonicity law: if `x <= y` then `get_timestamp(x) <= get_timestamp(y)`.
    ///
    /// Ghost-only — panics at runtime.
    #[trusted]
    fn get_timestamp_monotonic(self, _x: SyncView, _y: SyncView)
    where
        Self: Sized,
    {
        panic!("ghost code only")
    }
}

/// A sync view representing a thread's perspective on shared memory.
///
/// In Creusot, `SyncView` tracks the happens-before relationship between
/// atomic operations. It is used as a ghost parameter in atomic load/store
/// operations to express release-acquire semantics.
///
/// Reference: Creusot `creusot-std/src/sync_view.rs:42-43`
#[derive(Clone, Copy)]
pub struct SyncView(PhantomData<()>);

impl SyncView {
    /// Create a new sync view.
    ///
    /// Ghost-only — panics at runtime.
    pub fn new() -> Ghost<Self> {
        Ghost::conjure()
    }
}

impl Default for SyncView {
    fn default() -> Self {
        SyncView(PhantomData)
    }
}

/// Ghost type wrapping a value with a sync view timestamp.
///
/// `AtView<T>` pairs a value with a sync view reference, enabling
/// atomic invariant protocols to track when values were last written.
///
/// Reference: Creusot `creusot-std/src/sync_view.rs` (AtView concept)
pub struct AtView<T> {
    _marker: PhantomData<T>,
}

impl<T> AtView<T> {
    /// Create a new `AtView` wrapping a value.
    ///
    /// Ghost-only — panics at runtime.
    pub fn new(_value: Ghost<T>) -> Ghost<(SyncView, Self)> {
        Ghost::conjure()
    }

    /// Get the view logic for this `AtView`.
    ///
    /// Ghost-only — panics at runtime.
    pub fn view_logic(&self) -> SyncView {
        panic!("ghost code only")
    }

    /// Extract the inner value given a sync view.
    ///
    /// Ghost-only — panics at runtime.
    pub fn into_inner(self, _view: SyncView) -> T {
        panic!("ghost code only")
    }

    /// Get the inner value reference.
    ///
    /// Ghost-only — panics at runtime.
    pub fn val(&self) -> &T {
        panic!("ghost code only")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sync_view_is_zero_sized() {
        assert_eq!(std::mem::size_of::<SyncView>(), 0);
    }

    #[test]
    fn test_sync_view_copy() {
        let v = SyncView::default();
        let _v2 = v;
        let _v3 = v; // Copy
    }
}
