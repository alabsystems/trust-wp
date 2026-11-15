//@ expect: verify
//@ xfail: the price of D-147: a body that computes with a float keeps the clause-free cap,
//@ xfail: because the encoder reads a float as a real number. The charge here is true under
//@ xfail: IEEE-754 too, but the rule cannot tell it from clause_free_f64_to_f32_cast_read_as_identity.rs.
//@ mechanism: twin of clause_free_f64_to_f32_cast_read_as_identity.rs at a value `f32` represents
//@ mechanism: exactly: `0.5f64 as f32 as f64` is `0.5`, so the `assert!` arm never runs.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn roundtrip(x: f64) {
    if x == 0.5 {
        assert!((x as f32) as f64 == x);
    }
}
