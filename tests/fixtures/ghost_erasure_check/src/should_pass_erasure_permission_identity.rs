// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Permission identity should be SKIPPED for `#[erasure(...)]` functions.
//!
//! `#[erasure(target)]` marks a function as the ghost-bearing implementation
//! half of an erasure pair. Such a function legitimately receives both the
//! runtime resource and its ghost permission as inputs — the same-origin
//! witness lives on the caller / erased target, not in the function body.
//! The permission identity heuristic must not flag these calls.
//!
//! Regression for the `Perm::as_ref(x, own)` and `Perm::as_mut(x, own)`
//! patterns in
//! `reference/creusot/tests/should_succeed/specification/erasure.rs`.

#![allow(dead_code, unexpected_cfgs, unused_variables)]

use trust_wp_std::{erasure, ghost::perm::Perm, ghost::Ghost, requires, trusted};

#[trusted]
pub unsafe fn test_ptr<'a, T>(x: *mut T) -> &'a T {
    unsafe { &*x }
}

#[erasure(test_ptr)]
#[requires(false)]
pub unsafe fn test_ptr2<T>(x: *mut T, own: Ghost<&Perm<*const T>>) -> &T {
    unsafe { Perm::as_ref(x, own) }
}

#[trusted]
pub unsafe fn test_ptr_mut<'a, T>(x: *mut T) -> &'a mut T {
    unsafe { &mut *x }
}

#[erasure(test_ptr_mut)]
#[requires(false)]
pub unsafe fn test_ptr_mut2<T>(x: *mut T, own: Ghost<&mut Perm<*const T>>) -> &mut T {
    unsafe { Perm::as_mut(x, own) }
}

fn main() {}
