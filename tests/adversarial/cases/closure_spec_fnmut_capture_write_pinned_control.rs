//@ expect: verify
//@ xfail: the caller never advances a variable a spec-bearing `FnMut` closure captures, so the
//@ xfail: closure's `ensures(x@ == 50)` does not reach `f`'s `x` and `f` is refuted
//@ xfail: (`postcondition`) on a TRUE claim. Retiring it is the fix of its two RED twins.
//@ mechanism: the TRUE twin of closure_spec_fnmut_capture_write_contradicts_own_ensures, identical
//@ mechanism: but for `f`'s claim, which here is the value the closure's contract states. A fix that
//@ mechanism: closes the RED twins by forgetting `x` at the call must make THIS verify, or it has
//@ mechanism: only traded a false accept for a lost credit.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — measured `f FAILED ✗ (postcondition)` beside `f::{closure#2} verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 50)]
pub fn f() -> u8 {
    let mut x = 0u8;
    let mut c = #[ensures(x@ == 50)]
    || {
        x = 50;
    };
    c();
    x
}
