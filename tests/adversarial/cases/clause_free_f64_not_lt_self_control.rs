//@ expect: verify
//@ xfail: the price of D-147: a body that computes with a float keeps the clause-free cap,
//@ xfail: because the encoder reads a float as a real number. The charge here is true under
//@ xfail: IEEE-754 too, but the rule cannot tell it from clause_free_f64_eq_assert_despite_nan.rs.
//@ mechanism: twin of clause_free_f64_eq_assert_despite_nan.rs whose assertion holds for every `f64`:
//@ mechanism: `x < x` is false for every number and for NaN, so the `assert!` arm is never taken
//@ mechanism: and D-142 rightly cuts it.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn not_lt_self(x: f64) {
    assert!(!(x < x));
}
