//@ expect: reject
//@ mechanism: `*x` of a closure parameter `x: i32` has no reading (contract-syntax.md: "as is `*x`
//@ mechanism: of a parameter that is no reference (`x: i32`) ... however spelled"). D-100 refuses it
//@ mechanism: for a fn item (`refuses_an_unplaced_mut_ref_read`), which returns early for a closure,
//@ mechanism: so the closure's clause is read as `x == result` and verified.
//@ accept-means: an ill-typed clause the fail-closed rule must refuse is credited.
//@ WHY THE CONTRACT IS FALSE: it has no reading; the chained comparison keeps it from the Rust type-check.
//@ fixed-by: D-101 (a closure's parameters are read through the state elaboration a function's are)
//@ teeth: MEASURED on d73d0571 (debug driver): `host::{closure#0} verified`. On the D-101
//@ teeth: tree the clause is refused by name (`*x` reads through the parameter `x`, which is
//@ teeth: not a reference), as the fn-item spelling already was.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![feature(stmt_expr_attributes, proc_macro_hygiene)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn host() {
    let c = #[ensures(*x == result && 0 < 1 < 2)]
    |x: i32| x;
    let _ = c(3);
}
