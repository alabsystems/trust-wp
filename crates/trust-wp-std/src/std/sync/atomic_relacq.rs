// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Atomic types with release-acquire memory ordering.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides Creusot-compatible wrappers around `std::sync::atomic`
//! types that use release-acquire ordering. Each atomic type is paired with
//! ghost `LoadCommitter<T, C>` and `StoreCommitter<T, C>` types for specifying
//! atomic operation protocols.
//!
//! Unlike the SC variant (which uses single-param `LoadCommitter<C>`), the
//! relacq variant uses a two-parameter committer `LoadCommitter<T, C>` where
//! `T` is the value type and `C` is the atomic container type. This matches
//! Creusot's release-acquire API which requires `SyncView` tracking.
//!
//! Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`

use std::marker::PhantomData;

use crate::{
    ghost::{
        perm::{Container, Perm},
        Ghost,
    },
    sync_view::SyncView,
};

/// Creusot wrapper around `std::sync::atomic::AtomicBool` with
/// release-acquire ordering.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`
pub struct AtomicBool(std::sync::atomic::AtomicBool);

impl Container for AtomicBool {
    type Value = bool;

    fn is_disjoint(&self, _self_val: &Self::Value, other: &Self, _other_val: &Self::Value) -> bool {
        !std::ptr::eq(self, other)
    }
}

// Safety: Perm<AtomicBool> contains no actual data beyond the PhantomData.
unsafe impl Send for Perm<AtomicBool> {}
unsafe impl Sync for Perm<AtomicBool> {}

impl AtomicBool {
    /// Create a new `AtomicBool`.
    ///
    /// Returns the atomic value and a ghost permission token.
    /// In Creusot, takes an additional `Ghost<&mut SyncView>` for view tracking.
    #[allow(unused_variables)]
    pub fn new(val: bool, view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<AtomicBool>>>) {
        (
            Self(std::sync::atomic::AtomicBool::new(val)),
            Ghost::conjure(),
        )
    }

    /// Consume the atomic and return its inner value.
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicBool>>>) -> bool {
        self.0.into_inner()
    }

    /// Load the current value with acquire ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> bool
    where
        F: FnOnce(&LoadCommitter<bool, Self>),
    {
        self.0.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Store a value with release ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: bool, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<bool, Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::Release);
    }

    /// Swap with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: bool, f: Ghost<F>) -> bool
    where
        F: FnOnce(&mut UpdateCommitter<bool, Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::AcqRel)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicUsize` with
/// release-acquire ordering.
pub struct AtomicUsize(std::sync::atomic::AtomicUsize);

impl Container for AtomicUsize {
    type Value = usize;

    fn is_disjoint(&self, _self_val: &Self::Value, other: &Self, _other_val: &Self::Value) -> bool {
        !std::ptr::eq(self, other)
    }
}

unsafe impl Send for Perm<AtomicUsize> {}
unsafe impl Sync for Perm<AtomicUsize> {}

impl AtomicUsize {
    /// Create a new `AtomicUsize`.
    #[allow(unused_variables)]
    pub fn new(val: usize, view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<AtomicUsize>>>) {
        (
            Self(std::sync::atomic::AtomicUsize::new(val)),
            Ghost::conjure(),
        )
    }

    /// Consume the atomic and return its inner value.
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicUsize>>>) -> usize {
        self.0.into_inner()
    }

    /// Load with acquire ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> usize
    where
        F: FnOnce(&LoadCommitter<usize, Self>),
    {
        self.0.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Store with release ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: usize, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<usize, Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::Release);
    }

    /// Swap with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: usize, f: Ghost<F>) -> usize
    where
        F: FnOnce(&mut UpdateCommitter<usize, Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::AcqRel)
    }

    /// Fetch-add with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: usize, f: Ghost<F>) -> usize
    where
        F: FnOnce(&mut UpdateCommitter<usize, Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::AcqRel)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicI32` with
/// release-acquire ordering.
pub struct AtomicI32(std::sync::atomic::AtomicI32);

impl Container for AtomicI32 {
    type Value = i32;

    fn is_disjoint(&self, _self_val: &Self::Value, other: &Self, _other_val: &Self::Value) -> bool {
        !std::ptr::eq(self, other)
    }
}

unsafe impl Send for Perm<AtomicI32> {}
unsafe impl Sync for Perm<AtomicI32> {}

impl AtomicI32 {
    /// Create a new `AtomicI32`.
    #[allow(unused_variables)]
    pub fn new(val: i32, view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<AtomicI32>>>) {
        (
            Self(std::sync::atomic::AtomicI32::new(val)),
            Ghost::conjure(),
        )
    }

    /// Consume the atomic and return its inner value.
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }

    /// Load with acquire ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> i32
    where
        F: FnOnce(&LoadCommitter<i32, Self>),
    {
        self.0.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Store with release ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: i32, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<i32, Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::Release);
    }

    /// Swap with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: i32, f: Ghost<F>) -> i32
    where
        F: FnOnce(&mut UpdateCommitter<i32, Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::AcqRel)
    }

    /// Fetch-add with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: i32, f: Ghost<F>) -> i32
    where
        F: FnOnce(&mut UpdateCommitter<i32, Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::AcqRel)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicU32` with
/// release-acquire ordering.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`
pub struct AtomicU32(std::sync::atomic::AtomicU32);

impl Container for AtomicU32 {
    type Value = u32;

    fn is_disjoint(&self, _self_val: &Self::Value, other: &Self, _other_val: &Self::Value) -> bool {
        !std::ptr::eq(self, other)
    }
}

// Safety: Perm<AtomicU32> contains no actual data beyond the PhantomData.
unsafe impl Send for Perm<AtomicU32> {}
unsafe impl Sync for Perm<AtomicU32> {}

impl AtomicU32 {
    /// Create a new `AtomicU32`.
    #[allow(unused_variables)]
    pub fn new(val: u32, view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<AtomicU32>>>) {
        (
            Self(std::sync::atomic::AtomicU32::new(val)),
            Ghost::conjure(),
        )
    }

    /// Consume the atomic and return its inner value.
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicU32>>>) -> u32 {
        self.0.into_inner()
    }

    /// Load with acquire ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> u32
    where
        F: FnOnce(&LoadCommitter<u32, Self>),
    {
        self.0.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Store with release ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: u32, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<u32, Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::Release);
    }

    /// Swap with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: u32, f: Ghost<F>) -> u32
    where
        F: FnOnce(&mut UpdateCommitter<u32, Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::AcqRel)
    }

    /// Fetch-add with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: u32, f: Ghost<F>) -> u32
    where
        F: FnOnce(&mut UpdateCommitter<u32, Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::AcqRel)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicU64` with
/// release-acquire ordering.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`
pub struct AtomicU64(std::sync::atomic::AtomicU64);

impl Container for AtomicU64 {
    type Value = u64;

    fn is_disjoint(&self, _self_val: &Self::Value, other: &Self, _other_val: &Self::Value) -> bool {
        !std::ptr::eq(self, other)
    }
}

// Safety: Perm<AtomicU64> contains no actual data beyond the PhantomData.
unsafe impl Send for Perm<AtomicU64> {}
unsafe impl Sync for Perm<AtomicU64> {}

impl AtomicU64 {
    /// Create a new `AtomicU64`.
    #[allow(unused_variables)]
    pub fn new(val: u64, view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<AtomicU64>>>) {
        (
            Self(std::sync::atomic::AtomicU64::new(val)),
            Ghost::conjure(),
        )
    }

    /// Consume the atomic and return its inner value.
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicU64>>>) -> u64 {
        self.0.into_inner()
    }

    /// Load with acquire ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> u64
    where
        F: FnOnce(&LoadCommitter<u64, Self>),
    {
        self.0.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Store with release ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: u64, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<u64, Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::Release);
    }

    /// Swap with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: u64, f: Ghost<F>) -> u64
    where
        F: FnOnce(&mut UpdateCommitter<u64, Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::AcqRel)
    }

    /// Fetch-add with release-acquire ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: u64, f: Ghost<F>) -> u64
    where
        F: FnOnce(&mut UpdateCommitter<u64, Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::AcqRel)
    }
}

/// Ghost committer for atomic load operations (Rel/Acq variant).
///
/// Two type parameters matching Creusot: `T` is the value type (e.g., `bool`),
/// `C` is the container (e.g., `AtomicBool`).
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`
pub struct LoadCommitter<T, C: Container> {
    _marker: PhantomData<(T, C)>,
}

impl<T, C: Container> LoadCommitter<T, C> {
    /// Get the value that was loaded.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn val(&self) -> T {
        panic!("ghost code only")
    }

    /// Get a reference to the atomic that was loaded from.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn ward(&self) -> C {
        panic!("ghost code only")
    }

    /// Commit the load, consuming a ghost permission and sync view.
    ///
    /// Ghost-only -- panics at runtime.
    #[allow(unused_variables)]
    pub fn shoot(&self, perm: &Perm<C>, view: &mut SyncView) {
        panic!("ghost code only")
    }
}

/// Ghost committer for atomic store operations (Rel/Acq variant).
///
/// Two type parameters matching Creusot: `T` is the value type,
/// `C` is the container type.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`
pub struct StoreCommitter<T, C: Container> {
    _marker: PhantomData<(T, C)>,
}

impl<T, C: Container> StoreCommitter<T, C> {
    /// Get the value being stored.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn val(&self) -> T {
        panic!("ghost code only")
    }

    /// Get a reference to the atomic being stored to.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn ward(&self) -> C {
        panic!("ghost code only")
    }

    /// Check if the store has been committed.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn shot(&self) -> bool {
        panic!("ghost code only")
    }

    /// Commit the store, updating the permission and sync view.
    ///
    /// Ghost-only -- panics at runtime.
    #[allow(unused_variables)]
    pub fn shoot(&mut self, perm: &mut Perm<C>, view: &mut SyncView) {
        panic!("ghost code only")
    }
}

/// Ghost committer for atomic read-modify-write operations (Rel/Acq variant).
///
/// Two type parameters matching Creusot: `T` is the value type,
/// `C` is the container type.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_relacq.rs`
pub struct UpdateCommitter<T, C: Container> {
    _marker: PhantomData<(T, C)>,
}

impl<T, C: Container> UpdateCommitter<T, C> {
    /// Check if the update has been committed.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn shot(&self) -> bool {
        panic!("ghost code only")
    }

    /// Get a reference to the atomic being updated.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn ward(&self) -> C {
        panic!("ghost code only")
    }

    /// Get the value held before the update.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn old_val(&self) -> T {
        panic!("ghost code only")
    }

    /// Get the value held after the update.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn new_val(&self) -> T {
        panic!("ghost code only")
    }

    /// Commit the update, mutating the permission and sync view.
    ///
    /// Ghost-only -- panics at runtime.
    #[allow(unused_variables)]
    pub fn shoot(&mut self, perm: &mut Perm<C>, view: &mut SyncView) {
        panic!("ghost code only")
    }
}
