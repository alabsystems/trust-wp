// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A WELL-TYPED variant measure that does not decrease.
//!
//! `i32: WellFounded`, so `spec_tc` accepts this specification and the driver
//! actually RUNS — the decrease obligation is posed and refuted. This is the
//! complement of `dropped_variant_clause_rejects_function`, whose `char`
//! measure rustc rejects with the `char: WellFounded` E0277 before any
//! obligation is posed; only a well-typed measure reaches the obligation.

use trust_wp::{check, variant};

#[check(terminates)]
#[variant(0i32)]
fn constant_measure(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        constant_measure(n - 1)
    }
}

fn main() {
    let _ = constant_measure(3);
}
