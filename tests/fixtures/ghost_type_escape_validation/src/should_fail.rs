// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost-type escape fixtures that should FAIL.
//!
//! These mirror the upstream compat shapes from
//! `reference/creusot/tests/should_fail/generic_deref_ghost.rs` and
//! `generic_deref_snap.rs`.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use std::ops::Deref;

use creusot_std::prelude::*;

#[requires(T::deref.precondition((x,)))]
#[ensures(T::deref.postcondition((x,), result))]
pub fn deref_wrap<T: Deref>(x: &T) -> &T::Target {
    &*x
}

pub fn bad_ghost_escape(x: Ghost<i32>) -> i32 {
    *deref_wrap(&x)
}

pub fn bad_snapshot_escape(x: Snapshot<i32>) -> i32 {
    *deref_wrap(&x)
}

pub fn bad_ghost_ref_escape<'a>(x: Ghost<&'a i32>) -> &'a i32 {
    *deref_wrap(&x)
}

pub fn bad_ghost_ref_escape_with_runtime_source<'a>(
    _source: &'a i32,
    x: Ghost<&'a i32>,
) -> &'a i32 {
    *deref_wrap(&x)
}

fn main() {}
