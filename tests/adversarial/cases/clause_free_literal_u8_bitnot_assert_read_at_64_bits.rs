//@ expect: reject
//@ mechanism: the parameter-free spelling of clause_free_u8_bitnot_assert_read_at_64_bits.rs: the
//@ mechanism: operand is a local bound to the literal `0u8`, so the charge has no premise at all.
//@ mechanism: `!x` is read as a 64-bit complement and `!x != 255` is proved; D-142 cuts the
//@ mechanism: `assert!` arm, which runs on every call.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift, so the arm stays in the clause-free cap.
//@ fixed-by: D-242 reads the complement at its type (8 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics on every call is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `not_literal()` panics: `!0u8` is `255`.
//@ verdict: failed
//@ fn-failed: not_literal
//@ teeth: ACCEPTED (`not_literal verified`) under D-142 before D-147; `unknown (partial: panic
//@ teeth: paths unchecked)` with the proved dead edges withheld (an A/B knob) and after D-147. The
//@ teeth: twin clause_free_literal_u8_bitnot_assert_control.rs asserts the true `!x == 255`;
//@ teeth: clause_free_bool_not_assert_control.rs is the `bool` complement, which keeps D-142's credit.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn not_literal() {
    let x = 0u8;
    assert!(!x != 255);
}
