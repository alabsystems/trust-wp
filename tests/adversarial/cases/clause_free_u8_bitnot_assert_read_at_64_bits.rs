//@ expect: reject
//@ mechanism: D-142 cuts a clause-free body's `assert!` arm when the walk's charge `!guard` is
//@ mechanism: proved, and D-143 honors the proof when its premises are entry facts, as here (the
//@ mechanism: parameter range). The proof is only as good as the guard's translation: `!x` on a `u8`
//@ mechanism: reaches the solver as a complement taken at 64 bits (`encode_int_unop_bv_not`,
//@ mechanism: `DEFAULT_BV_WIDTH`, whatever the operand's type), so at `x == 0` it is `2^64 - 1`, not
//@ mechanism: `255`, and the charge `!x != 255` is proved. Before D-142 the cap counted the arm
//@ mechanism: unchecked. u8_bitnot_read_at_64_bits.rs is the contracted spelling (the core defect);
//@ mechanism: D-142 widens it to every clause-free body.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift, so the arm stays in the clause-free cap.
//@ fixed-by: D-242 reads the complement at its type (8 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics at `x = 0` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `not_bits(0)` panics: `!0u8` is `255`, so `!x != 255` is false.
//@ verdict: failed
//@ fn-failed: not_bits
//@ teeth: ACCEPTED (`not_bits verified`) under D-142 before D-147; `unknown (partial: panic paths
//@ teeth: unchecked)` with the proved dead edges withheld (an A/B knob) and after D-147. The twin
//@ teeth: clause_free_u8_bitnot_assert_control.rs asserts the true `!x == 255`.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn not_bits(x: u8) {
    if x == 0 {
        assert!(!x != 255);
    }
}
