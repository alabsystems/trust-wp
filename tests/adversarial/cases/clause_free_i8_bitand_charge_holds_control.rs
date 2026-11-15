//@ expect: verify
//@ mechanism: control for D-142 over a bit operation D-147 does not refuse: `x & 1` on an `i8` is
//@ mechanism: read exactly at the parameter's signed width, so the `assert!` charge `x & 1 == 1` at
//@ mechanism: `x == -1` is proved and its arm is cut. The reject twin
//@ mechanism: clause_free_i8_bitand_charge_fails.rs differs in the guarded value alone.
//@ teeth: control; the authority trace reports its `assert!` arm edge dead, and the panic call behind
//@ teeth: it is what caps the verdict when no edge is cut.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn low_bit(x: i8) {
    if x == -1 {
        assert!(x & 1 == 1);
    }
}
