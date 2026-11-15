//@ expect: reject
//@ mechanism: the signed spelling of clause_free_u128_bitand_read_at_64_bits.rs: `x | 1` on an
//@ mechanism: `i128` below `-2^64` is taken at 64 bits, so the charge
//@ mechanism: `x | 1 != -2^64 + 1` is proved and D-142 cut the arm; Rust's `x | 1` is `-2^64 + 1`.
//@ fixed-by: D-149 (narrows D-147): no switch edge is proved dead in a body that computes with a
//@ fixed-by: 128-bit integer, so the arm stays in the clause-free cap.
//@ fixed-by: D-242 reads the `|` at its type (128 bits), so the panic is found: `failed`.
//@ accept-means: a clause-free body that panics at `x = -2^64` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `or_low(-(1 << 64))` panics.
//@ verdict: failed
//@ fn-failed: or_low
//@ teeth: ACCEPTED (`or_low verified`) under D-142 and D-147, which does not count a 128-bit
//@ teeth: value; `unknown (partial: panic paths unchecked)` after.
//@ teeth: `failed` since D-242 (a validated counterexample reaches the panic); `unknown`
//@ teeth: on trust-wp 7726ea81, its parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn or_low(x: i128) {
    if x == -18446744073709551616 {
        assert!(x | 1 != -18446744073709551615);
    }
}
