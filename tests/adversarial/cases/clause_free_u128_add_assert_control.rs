//@ expect: verify
//@ xfail: the price of D-149: a body that computes with a 128-bit integer keeps the clause-free cap,
//@ xfail: because the encoder reads a bit operation on one at 64 bits. Addition is read exactly and
//@ xfail: the charge holds, but the rule refuses the 128-bit value whole
//@ xfail: (clause_free_u128_trailing_zeros_read_at_64_bits.rs).
//@ mechanism: twin of clause_free_u128_bitand_read_at_64_bits.rs over `+`: `2^64 + 1` is not `0`.
//@ teeth: control; verified under D-142 and D-147, before D-149 counted a 128-bit value.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn add_high(x: u128) {
    if x == 18446744073709551616 {
        assert!(x + 1 != 0);
    }
}
