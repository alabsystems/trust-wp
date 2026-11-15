// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A variant measure that TYPE-CHECKS but that `parse_variant_clause` refuses.
//!
//! `match n { 0 => 0, _ => n }` is a well-typed `i32` expression, so nothing
//! rejects it before the driver; the contract parser then refuses it because
//! Pearlite does not support matching integer literals. That is the only input
//! shape that reaches `variants_dropped` in
//! `callbacks::parsing::clauses::has_dropped_clauses`.

use trust_wp::{check, variant};

#[check(terminates)]
#[variant(match n { 0 => 0, _ => n })]
fn refused_measure(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        refused_measure(n - 1)
    }
}

fn main() {
    let _ = refused_measure(3);
}
