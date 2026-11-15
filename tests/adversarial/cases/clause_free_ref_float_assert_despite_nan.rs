//@ expect: reject
//@ mechanism: the dereference spelling of clause_free_f64_eq_assert_despite_nan.rs: the parameter
//@ mechanism: is a `&f64` and the comparison reads `*x` twice. Read as a real number, `*x == *x`
//@ mechanism: holds, so D-142 cut the `assert!` arm; under IEEE-754 it is false at NaN.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift; D-215 reads the comparison over IEEE-754, where the
//@ fixed-by: arm's charge is refuted.
//@ accept-means: a clause-free body that panics at `*x = f64::NAN` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `deref_eq(&f64::NAN)` panics.
//@ verdict: failed
//@ teeth: ACCEPTED (`deref_eq verified`) under D-142 before D-147; `unknown (partial: panic
//@ teeth: paths unchecked)` with D-142's proved edges withheld, and after D-147. Under D-215 the
//@ teeth: charge is refuted at NaN (`deref_eq FAILED`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn deref_eq(x: &f64) {
    assert!(*x == *x);
}
