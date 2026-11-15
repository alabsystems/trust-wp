//@ expect: reject
//@ mechanism: the encoder takes a bit operation at 64 bits whatever the operand's type
//@ mechanism: (`encode_int_binop_bv`, `DEFAULT_BV_WIDTH`), so `x & 2^64` on a `u128` reads as
//@ mechanism: `0` at `x == 2^64`, the `assert!` arm's charge `x & 2^64 == 0` is proved, and D-142
//@ mechanism: cut the arm. u128_bitand_read_at_64_bits.rs is the contracted spelling (the core
//@ mechanism: defect); D-142 widened it to clause-free bodies.
//@ fixed-by: D-149 (narrows D-147): no switch edge is proved dead in a body that computes with a
//@ fixed-by: 128-bit integer, so the arm stays in the clause-free cap.
//@ fixed-by: D-242 reads the `&` at its type (128 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics at `x = 2^64` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `and_high(1 << 64)` panics: `x & x` is `x`, not `0`.
//@ verdict: failed
//@ fn-failed: and_high
//@ teeth: ACCEPTED (`and_high verified`) under D-142 and D-147, which does not count a 128-bit
//@ teeth: value; `unknown (partial: panic paths unchecked)` after.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn and_high(x: u128) {
    if x == 18446744073709551616 {
        assert!(x & 18446744073709551616 == 0);
    }
}
