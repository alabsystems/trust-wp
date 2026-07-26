// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread specifications for trust-wp.
//!
//! Provides `spawn`, `scope`, and `JoinHandleExt` to match Creusot's
//! `creusot-std/src/std/thread.rs` interface.
//!
//! Reference: Creusot `creusot-std/src/std/thread.rs`

use std::thread::{self, JoinHandle, ScopedJoinHandle};

use crate::{
    ghost::{invariant::Tokens, Ghost},
    trusted,
};

/// Extension trait for [`JoinHandle`] and [`ScopedJoinHandle`].
///
/// Provides `join_unwrap()` which is a wrapper around `self.join().unwrap()`,
/// avoiding the need for trust-wp/Creusot to reason about `std::thread::Result`
/// (which contains a `dyn` type).
///
/// Reference: Creusot `creusot-std/src/std/thread.rs:4-18`
pub trait JoinHandleExt<T> {
    /// Predicate that specifies the valid return results for the handle.
    ///
    /// Specification-only — panics at runtime.
    #[trusted]
    fn valid_result(&self, _x: &T) -> bool {
        panic!("JoinHandleExt::valid_result is specification-only")
    }

    /// Wrapper around `self.join().unwrap()`.
    ///
    /// Panics only on stack-overflow or OOM on the spawned thread.
    fn join_unwrap(self) -> T;
}

impl<T> JoinHandleExt<T> for JoinHandle<T> {
    fn join_unwrap(self) -> T {
        self.join().unwrap()
    }
}

impl<T> JoinHandleExt<T> for ScopedJoinHandle<'_, T> {
    fn join_unwrap(self) -> T {
        self.join().unwrap()
    }
}

/// Creusot-compatible wrapper around [`std::thread::spawn`].
///
/// The closure receives a fresh `Ghost<Tokens>` argument to enable
/// ghost protocol reasoning in concurrent code.
///
/// Reference: Creusot `creusot-std/src/std/thread.rs:58-70`
pub fn spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce(Ghost<Tokens<'static>>) -> T + Send + 'static,
    T: Send + 'static,
{
    thread::spawn(|| f(Ghost::conjure()))
}

/// Creusot-compatible scope wrapper.
///
/// Wraps `std::thread::Scope` to provide ghost token threading.
///
/// Reference: Creusot `creusot-std/src/std/thread.rs:72-88`
pub struct Scope<'scope, 'env: 'scope> {
    inner: &'scope thread::Scope<'scope, 'env>,
}

impl<'scope, 'env: 'scope> Scope<'scope, 'env> {
    /// Spawn a scoped thread with ghost token access.
    pub fn spawn<F, T>(&mut self, f: F) -> ScopedJoinHandle<'scope, T>
    where
        F: FnOnce(Ghost<Tokens<'scope>>) -> T + Send + 'scope,
        T: Send + 'scope,
    {
        self.inner.spawn(|| f(Ghost::conjure()))
    }
}

/// Creusot-compatible wrapper around [`std::thread::scope`].
///
/// Reference: Creusot `creusot-std/src/std/thread.rs:91-99`
pub fn scope<'env, F, T>(f: F) -> T
where
    F: for<'scope> FnOnce(&mut Scope<'scope, 'env>) -> T,
{
    thread::scope(|s| f(&mut Scope { inner: s }))
}
