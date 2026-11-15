//@ expect: verify
//@ xfail: D-147's cap: a clause-free body that computes with an integer complement proves no switch
//@ xfail: edge dead, so the `assert!` arm stays unchecked
//@ xfail: (`unknown (partial: panic paths unchecked)`). Until D-242 the complement was read at 64
//@ xfail: bits and the true assertion was refuted (`failed`); the pinned flavour keeps that
//@ xfail: refutation out.
//@ xfail-verdict: unknown
//@ mechanism: twin of clause_free_literal_u8_bitnot_assert_read_at_64_bits.rs whose assertion is
//@ mechanism: true: `!0u8` is `255`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn not_literal() {
    let x = 0u8;
    assert!(!x == 255);
}
