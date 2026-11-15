// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A LOOP-level `#[variant(...)]` the contract parser refuses.
//!
//! The loop invariant beside it parses, so the only dropped clause is the
//! per-loop variant: this is the input that makes `per_loop_variants_dropped`
//! true in `has_dropped_clauses`.

#![feature(proc_macro_hygiene)]

use trust_wp::{ensures, invariant, variant};

#[ensures(result >= 0)]
fn malformed_per_loop_variant(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    #[invariant(i >= 0)]
    #[variant(match i { 0 => 0, _ => n - i })]
    while i < n {
        sum += i;
        i += 1;
    }
    sum
}

fn main() {
    let _ = malformed_per_loop_variant(5);
}
