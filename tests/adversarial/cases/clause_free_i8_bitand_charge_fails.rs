//@ expect: reject
//@ mechanism: the reject twin of clause_free_i8_bitand_charge_holds_control.rs: at `x == -2` the
//@ mechanism: charge `x & 1 == 1` is false (`-2 & 1 == 0`), so D-142 proves no edge dead and the
//@ mechanism: verdict is refuted, where the twin at `x == -1` verifies. A reading of `&` that lost
//@ mechanism: the sign (a 64-bit pattern converted back unsigned) would flip one of the pair.
//@ fixed-by: n/a — a pin of D-142's reading of a signed bit operation.
//@ accept-means: a clause-free body that panics at `x = -2` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `low_bit(-2)` panics.
//@ verdict: failed
//@ teeth: the twin verifies; this case is refuted with a counterexample at `x = -2`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn low_bit(x: i8) {
    if x == -2 {
        assert!(x & 1 == 1);
    }
}
