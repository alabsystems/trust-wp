//@ expect: reject
//@ mechanism: the round-trip spelling of clause_free_u8_shl_assert_keeps_shifted_out_bit.rs: `x << 4`
//@ mechanism: on a `u8` is read without dropping the bits shifted out of the type, so
//@ mechanism: `(255 << 4) >> 4` reads as `255`, the `assert!` arm's charge is proved and D-142 cut
//@ mechanism: the arm. In Rust `255u8 << 4` is `240` and the round trip is `15`.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift.
//@ fixed-by: D-242 reads the shift at its type (8 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics at `x = 255` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `round_trip(255)` panics.
//@ verdict: failed
//@ fn-failed: round_trip
//@ teeth: ACCEPTED (`round_trip verified`) under D-142 before D-147; `unknown (partial: panic paths
//@ teeth: unchecked)` with D-142's proved edges withheld, and after D-147.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn round_trip(x: u8) {
    if x == 255 {
        assert!((x << 4) >> 4 == 255);
    }
}
