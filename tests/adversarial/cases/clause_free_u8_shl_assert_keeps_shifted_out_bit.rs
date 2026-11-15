//@ expect: reject
//@ mechanism: D-142 cuts a clause-free body's `assert!` arm when the walk's charge is proved from
//@ mechanism: entry facts. `x << 1` on a `u8` is read without dropping the bits shifted out of the
//@ mechanism: type: at `x == 128` it is `256`, where Rust's is `0` (a shift checks only its amount,
//@ mechanism: never the bits it loses). The charge `x << 1 != 0` is proved and the arm is cut.
//@ mechanism: u8_shl_keeps_shifted_out_bit.rs is the contracted spelling (the core defect); D-142
//@ mechanism: widens it to every clause-free body.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift, so the arm stays in the clause-free cap.
//@ fixed-by: D-242 reads the shift at its type (8 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics at `x = 128` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `shl_bits(128)` panics: `128u8 << 1` is `0`.
//@ verdict: failed
//@ fn-failed: shl_bits
//@ teeth: ACCEPTED (`shl_bits verified`) under D-142 before D-147; `unknown (partial: panic paths
//@ teeth: unchecked)` with the proved dead edges withheld (an A/B knob) and after D-147. The twin
//@ teeth: clause_free_u8_shl_assert_control.rs asserts the true `x << 1 == 0`.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn shl_bits(x: u8) {
    if x == 128 {
        assert!(x << 1 != 0);
    }
}
