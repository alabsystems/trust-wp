// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic-surface gaps that are TYPE errors of the specification: rustc
//! reports them through the contract type-check vehicle
//! (`trust-wp-macros/src/spec_tc`), with Creusot's own wording (Creusot's
//! `DivLogic`/`RemLogic` are implemented for `Int` only — its
//! `tests/should_succeed/syntax/02_operators.rs` keeps `division_logic` on
//! machine integers commented out — and `a[i]` in logic is an `IndexLogic`
//! method call). They live apart from `should_fail_logic_surface.rs` because
//! rustc stops at a type error before the driver runs its own logic-surface
//! checks, so the two kinds of diagnostic can never appear in one build.

#![allow(dead_code, unexpected_cfgs)]

pub struct Bag {
    value: i32,
}

#[trust_wp::logic]
fn primitive_div(x: i32, y: i32) -> i32 {
    x / y
}

#[trust_wp::logic]
fn primitive_rem(x: i32, y: i32) -> i32 {
    x % y
}

#[trust_wp::logic]
fn unsupported_index(bag: Bag, idx: usize) -> i32 {
    bag[idx]
}

fn main() {}
