// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Atomic types with sequentially-consistent memory ordering.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides Creusot-compatible wrappers around `std::sync::atomic`
//! types that use sequentially-consistent (SeqCst) ordering. Each atomic type
//! is paired with ghost `LoadCommitter` and `StoreCommitter` types for
//! specifying atomic operation protocols.
//!
//! The `Container` trait associates each atomic wrapper with its value type
//! (e.g., `AtomicBool::Value = bool`). Committer types use `C::Value` for
//! `val()`, `old_val()`, `new_val()` — matching Creusot's API.
//!
//! Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`

use std::marker::PhantomData;

use crate::ghost::{
    perm::{Container, Perm},
    Ghost,
};

/// Creusot wrapper around `std::sync::atomic::AtomicBool` with
/// sequentially-consistent ordering.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`
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
    /// Signature matches Creusot: takes only `val`, not a `SyncView`.
    pub fn new(val: bool) -> (Self, Ghost<Box<Perm<AtomicBool>>>) {
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

    /// Load the current value with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> bool
    where
        F: FnOnce(&LoadCommitter<Self>),
    {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Store a value with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: bool, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
    }

    /// Swap with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: bool, f: Ghost<F>) -> bool
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicUsize` with
/// sequentially-consistent ordering.
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
    ///
    /// Signature matches Creusot: takes only `val`, not a `SyncView`.
    pub fn new(val: usize) -> (Self, Ghost<Box<Perm<AtomicUsize>>>) {
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

    /// Load with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> usize
    where
        F: FnOnce(&LoadCommitter<Self>),
    {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Store with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: usize, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
    }

    /// Swap with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: usize, f: Ghost<F>) -> usize
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::SeqCst)
    }

    /// Fetch-add with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: usize, f: Ghost<F>) -> usize
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicI32` with
/// sequentially-consistent ordering.
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
    ///
    /// Returns the atomic value and a ghost permission token.
    /// Signature matches Creusot: takes only `val`, not a `SyncView`.
    pub fn new(val: i32) -> (Self, Ghost<Box<Perm<AtomicI32>>>) {
        (
            Self(std::sync::atomic::AtomicI32::new(val)),
            Ghost::conjure(),
        )
    }

    /// Consume the atomic and return its inner value.
    ///
    /// Requires a ghost ownership proof to consume.
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }

    /// Load with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> i32
    where
        F: FnOnce(&LoadCommitter<Self>),
    {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Store with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: i32, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
    }

    /// Swap with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: i32, f: Ghost<F>) -> i32
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::SeqCst)
    }

    /// Fetch-add with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: i32, f: Ghost<F>) -> i32
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicU32` with
/// sequentially-consistent ordering.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`
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
    pub fn new(val: u32) -> (Self, Ghost<Box<Perm<AtomicU32>>>) {
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

    /// Load with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> u32
    where
        F: FnOnce(&LoadCommitter<Self>),
    {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Store with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: u32, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
    }

    /// Swap with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: u32, f: Ghost<F>) -> u32
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::SeqCst)
    }

    /// Fetch-add with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: u32, f: Ghost<F>) -> u32
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Creusot wrapper around `std::sync::atomic::AtomicU64` with
/// sequentially-consistent ordering.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`
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
    pub fn new(val: u64) -> (Self, Ghost<Box<Perm<AtomicU64>>>) {
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

    /// Load with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> u64
    where
        F: FnOnce(&LoadCommitter<Self>),
    {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Store with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: u64, f: Ghost<F>)
    where
        F: FnOnce(&mut StoreCommitter<Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
    }

    /// Swap with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn swap<F>(&self, val: u64, f: Ghost<F>) -> u64
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.swap(val, std::sync::atomic::Ordering::SeqCst)
    }

    /// Fetch-add with SeqCst ordering.
    #[allow(unused_variables)]
    pub fn fetch_add<F>(&self, val: u64, f: Ghost<F>) -> u64
    where
        F: FnOnce(&mut UpdateCommitter<Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Ghost committer for atomic load operations (SC variant).
///
/// Parameterized by the container type `C` (the atomic wrapper).
/// `val()` returns `C::Value` (e.g., `bool` for `AtomicBool`), matching
/// Creusot's `LoadCommitter<C: Container>::val(self) -> C::Value`.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`
pub struct LoadCommitter<C: Container<Value: Sized>> {
    _marker: PhantomData<C>,
}

impl<C: Container<Value: Sized>> LoadCommitter<C> {
    /// Get the value that was loaded.
    ///
    /// Returns `C::Value` (e.g., `bool` for `AtomicBool`).
    /// Ghost-only -- panics at runtime.
    pub fn val(&self) -> C::Value {
        panic!("ghost code only")
    }

    /// Get a reference to the atomic that was loaded from.
    ///
    /// Ghost-only -- panics at runtime.
    pub fn ward(&self) -> C {
        panic!("ghost code only")
    }

    /// Commit the load, consuming a ghost permission.
    ///
    /// Ghost-only -- panics at runtime.
    #[allow(unused_variables)]
    pub fn shoot(&self, perm: &Perm<C>) {
        panic!("ghost code only")
    }
}

/// Ghost committer for atomic store operations (SC variant).
///
/// Parameterized by the container type `C` (the atomic wrapper).
/// `val()` returns `C::Value` (e.g., `bool` for `AtomicBool`), matching
/// Creusot's `StoreCommitter<C: Container>::val(self) -> C::Value`.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`
pub struct StoreCommitter<C: Container<Value: Sized>> {
    _marker: PhantomData<C>,
}

impl<C: Container<Value: Sized>> StoreCommitter<C> {
    /// Get the value being stored.
    ///
    /// Returns `C::Value` (e.g., `bool` for `AtomicBool`).
    /// Ghost-only -- panics at runtime.
    pub fn val(&self) -> C::Value {
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

    /// Commit the store, updating the permission.
    ///
    /// Ghost-only -- panics at runtime.
    #[allow(unused_variables)]
    pub fn shoot(&mut self, perm: &mut Perm<C>) {
        panic!("ghost code only")
    }
}

/// Ghost committer for atomic read-modify-write operations (SC variant).
///
/// Used by `fetch_add` and similar operations.
/// `old_val()` and `new_val()` return `C::Value`, matching Creusot.
///
/// Reference: Creusot `creusot-std/src/std/sync/atomic_sc.rs`
pub struct UpdateCommitter<C: Container<Value: Sized>> {
    _marker: PhantomData<C>,
}

impl<C: Container<Value: Sized>> UpdateCommitter<C> {
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
    /// Returns `C::Value`.
    /// Ghost-only -- panics at runtime.
    pub fn old_val(&self) -> C::Value {
        panic!("ghost code only")
    }

    /// Get the value held after the update.
    ///
    /// Returns `C::Value`.
    /// Ghost-only -- panics at runtime.
    pub fn new_val(&self) -> C::Value {
        panic!("ghost code only")
    }

    /// Commit the update, mutating the permission.
    ///
    /// Ghost-only -- panics at runtime.
    #[allow(unused_variables)]
    pub fn shoot(&mut self, perm: &mut Perm<C>) {
        panic!("ghost code only")
    }
}
