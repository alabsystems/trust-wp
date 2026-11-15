//@ expect: reject
//@ mechanism: the integer-switch spelling of clause_free_u8_bitnot_assert_read_at_64_bits.rs, at
//@ mechanism: `u16`: `match !x` with a `panic!` arm on `65535`. The complement is read at 64 bits,
//@ mechanism: so at `x == 0` the discriminant is `2^64 - 1`, the switch lane's charge that the arm
//@ mechanism: is not taken is proved, and D-142 cut the arm. Rust's `!0u16` is `65535`.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift.
//@ fixed-by: D-242 reads the complement at its type (16 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics at `x = 0` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `not_match(0)` panics.
//@ verdict: failed
//@ fn-failed: not_match
//@ teeth: ACCEPTED (`not_match verified`) under D-142 before D-147; `unknown (partial: panic
//@ teeth: paths unchecked)` with D-142's proved edges withheld, and after D-147.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn not_match(x: u16) {
    if x == 0 {
        match !x {
            65535 => panic!(),
            _ => {}
        }
    }
}
