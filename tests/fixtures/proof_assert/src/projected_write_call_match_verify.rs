#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #1515: projected-write facts must survive `Call` and
//! `SwitchInt` boundaries before reaching a proof_assert.
//!
//! Sequence:
//! - `pair.0 = 5` creates projected-write fact
//! - `noop()` introduces a `Call` terminator
//! - `match take_true { ... }` introduces a `SwitchInt` terminator
//! - proof_assert in the true arm must still see `pair.0 == 5`

use trust_wp::{ensures, proof_assert, requires};

#[requires(true)]
#[ensures(true)]
#[inline(never)]
fn noop() {}

fn projected_write_call_match_verify(take_true: bool) -> (i32,) {
    let mut pair = (0_i32,);
    pair.0 = 5;
    noop();

    match take_true {
        true => proof_assert!(pair.0@ == 5),
        false => {}
    }

    pair
}

fn main() {
    let _ = projected_write_call_match_verify(true);
}
