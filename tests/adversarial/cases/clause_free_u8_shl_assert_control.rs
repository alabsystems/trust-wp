//@ expect: verify
//@ xfail: D-147's cap: a clause-free body that computes with a shift proves no switch edge dead, so
//@ xfail: the `assert!` arm stays unchecked (`unknown (partial: panic paths unchecked)`). Until
//@ xfail: D-242 the shift was read at 64 bits and the true assertion was refuted (`failed`); the
//@ xfail: pinned flavour keeps that refutation out.
//@ xfail-verdict: unknown
//@ mechanism: twin of clause_free_u8_shl_assert_keeps_shifted_out_bit.rs whose assertion is true:
//@ mechanism: `128u8 << 1` is `0`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn shl_bits(x: u8) {
    if x == 128 {
        assert!(x << 1 == 0);
    }
}
