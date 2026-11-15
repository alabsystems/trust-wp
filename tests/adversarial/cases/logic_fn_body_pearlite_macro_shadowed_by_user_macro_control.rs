//@ expect: verify
//@ mechanism: control for logic_fn_body_pearlite_macro_shadowed_by_user_macro, differing in the crate's `macro_rules! pearlite` alone: `pearlite! { 1 }` is the prelude's, and the body is `1`.
//@ accept-means: n/a (control) — `caller()` is `1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == 1)]
pub fn caller() -> Int {
    pearlite! { 1 }
}
