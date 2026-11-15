//@ expect: verify
//@ xfail: the price of D-147: a body that computes with a float keeps the clause-free cap,
//@ xfail: because the encoder reads a float as a real number. The charge here is true under
//@ xfail: IEEE-754 too, but the rule cannot tell it from clause_free_f64_plus_one_assert_rounds.rs.
//@ mechanism: twin of clause_free_f64_plus_one_assert_rounds.rs: rounding to nearest is monotone, so
//@ mechanism: `x + 1.0 >= x` holds for every `f64` the guard admits, infinity included.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn plus_one_ge(x: f64) {
    if x >= 0.0 {
        assert!(x + 1.0 >= x);
    }
}
