//@ expect: reject
//@ mechanism: the credited-call spelling of clause_free_u128_bitand_read_at_64_bits.rs:
//@ mechanism: `trailing_zeros` is a total integer method, so its call is no unchecked site, and it
//@ mechanism: is read at 64 bits: `0u128.trailing_zeros()` reads as `64`, where Rust's is `128`. The
//@ mechanism: charge `x.trailing_zeros() != 128` is proved and D-142 cut the arm. No operator
//@ mechanism: spells the bit operation here, so D-149 refuses the 128-bit value itself.
//@ fixed-by: D-149 (narrows D-147): no switch edge is proved dead in a body that computes with a
//@ fixed-by: 128-bit integer, so the arm stays in the clause-free cap.
//@ accept-means: a clause-free body that panics at `x = 0` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `tz(0)` panics.
//@ verdict: unknown
//@ teeth: ACCEPTED (`tz verified`) under D-142 and D-147, which does not count a 128-bit
//@ teeth: value; `unknown (partial: panic paths unchecked)` after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn tz(x: u128) {
    if x == 0 {
        assert!(x.trailing_zeros() != 128);
    }
}
