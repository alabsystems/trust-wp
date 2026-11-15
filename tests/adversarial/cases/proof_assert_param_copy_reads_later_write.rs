//@ expect: reject
//@ mechanism: the assertion lane reads a copy of a by-value parameter (`let c = a;`, or `let c = a + 0;`) as
//@ mechanism: the parameter's CURRENT value: after the parameter is overwritten (`a = 0`, `a *= 0`, a float
//@ mechanism: `a %= y`) the copy follows it, so `proof_assert!(a == c)` holds by reflexivity and
//@ mechanism: `proof_assert!(c@ == 0)` reads the new value. No precondition is involved, so the vacuity
//@ mechanism: guard that withholds an entry precondition read as a current fact does not fire. The function
//@ mechanism: lane keeps the copy: the same body returning `c`, comparing `a == c` in the program, or
//@ mechanism: passing both to a callee requiring `x == y` is refuted, and a copy of a local rather than a
//@ mechanism: parameter is refuted in the assertion lane too (proof_assert_param_copy_reads_later_write_control.rs).
//@ accept-means: `copy_then_overwrite(1)` reaches the assertion with `a == 0` and `c == 1`; an accept claims
//@ accept-means: they are equal. `copy_reads_new_value(1)` has `c == 1`, not `0`; `expr_copy_then_mul(1)`
//@ accept-means: has `a == 0` and `c == 1`; `f64_copy_then_rem(7.0, 5.0)` has `a == 2.0` and `c == 7.0`.
//@ fixed-by: D-241: a re-bound by-value parameter's entry value is read by its own symbol inside the substitution map's values, so the copy keeps the value it copied.
//@ teeth: ACCEPTED when committed, exit 0 (each of the four assertions and functions verified), and on the
//@ teeth: campaign tip before D-215: it is no float defect.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn copy_then_overwrite(mut a: i64) {
    let c = a;
    a = 0;
    proof_assert!(a == c);
}

#[ensures(true)]
pub fn copy_reads_new_value(mut a: i64) {
    let c = a;
    a = 0;
    proof_assert!(c@ == 0);
}

#[ensures(true)]
pub fn expr_copy_then_mul(mut a: i64) {
    let c = a + 0;
    a *= 0;
    proof_assert!(a == c);
}

#[ensures(true)]
pub fn f64_copy_then_rem(mut a: f64, y: f64) {
    let c = a;
    a %= y;
    proof_assert!(a == c);
}
