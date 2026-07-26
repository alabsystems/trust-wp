// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost-type escape fixtures that should PASS.
//!
//! These cover nearby allow-listed signatures in the validation pass:
//! unit-returning program functions, `#[check(ghost)]` functions,
//! `#[logic]` functions, and reference-preserving Ghost/Snapshot round-trips.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use std::ops::Deref;

use creusot_std::{ghost::invariant::Tokens, prelude::*};

pub struct PermissionState<T> {
    value: T,
}

#[requires(T::deref.precondition((x,)))]
#[ensures(T::deref.postcondition((x,), result))]
pub fn deref_wrap<T: Deref>(x: &T) -> &T::Target {
    &*x
}

pub fn ghost_param_unit_ok(x: Ghost<i32>) {
    let _ = *deref_wrap(&x);
}

#[check(ghost)]
pub fn ghost_checked_value_ok(x: Ghost<i32>) -> i32 {
    *deref_wrap(&x)
}

#[logic]
fn snapshot_logic_value_ok(x: Snapshot<i32>) -> i32 {
    0
}

pub fn ghost_ref_roundtrip_ok<'a>(x: &'a Ghost<i32>) -> &'a Ghost<i32> {
    x
}

pub fn snapshot_ref_roundtrip_ok<'a>(x: &'a Snapshot<i32>) -> &'a Snapshot<i32> {
    x
}

pub fn invariant_token_program_return_ok(_tokens: Ghost<Tokens<'_>>) -> i32 {
    0
}

pub fn ghost_permission_ref_source_ok<'a>(
    source: &'a i32,
    _permission: Ghost<&'a PermissionState<i32>>,
) -> &'a i32 {
    source
}

fn runtime_identity(x: i32) -> i32 {
    x
}

#[erasure(runtime_identity)]
pub fn erasure_ghost_authority_ok(x: i32, _proof: Ghost<Int>) -> i32 {
    x
}

pub fn snapshot_seq_authority_ok(_s: Snapshot<Seq<i32>>) -> usize {
    0
}

fn main() {}
