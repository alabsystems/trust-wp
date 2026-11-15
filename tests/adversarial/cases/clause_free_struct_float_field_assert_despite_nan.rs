//@ expect: reject
//@ mechanism: the projection spelling of clause_free_f64_eq_assert_despite_nan.rs: the float is a
//@ mechanism: field of a struct parameter, whose own type holds no float. The encoder reads the
//@ mechanism: field as a real number, where `p.v == p.v` holds, so the `assert!` arm's charge is
//@ mechanism: proved and D-142 cut the arm. D-147 asks every place the body reads for its type, a
//@ mechanism: projected one included.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift.
//@ accept-means: a clause-free body that panics at `p.v = f64::NAN` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `self_eq(P { v: f64::NAN })` panics.
//@ verdict: unknown
//@ teeth: ACCEPTED (`self_eq verified`) under D-142 before D-147; `unknown (partial: panic
//@ teeth: paths unchecked)` with D-142's proved edges withheld, and after D-147.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub struct P {
    pub v: f64,
}

pub fn self_eq(p: P) {
    assert!(p.v == p.v);
}
