//@ expect: verify
//@ mechanism: control for D-147: `!` on a `bool` is read exactly, so a body that negates a `bool`
//@ mechanism: keeps D-142's credit. The charge `!!b == b` is proved and the `assert!` arm is cut.
//@ mechanism: The integer twin is clause_free_literal_u8_bitnot_assert_read_at_64_bits.rs.
//@ teeth: control; `unknown (partial: panic paths unchecked)` with D-142's proved edges withheld.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn double_not(b: bool) {
    assert!(!!b == b);
}
