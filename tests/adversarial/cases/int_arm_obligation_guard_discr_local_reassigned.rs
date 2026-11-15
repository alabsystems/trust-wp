//@ expect: reject
//@ mechanism: the edge that guards an integer match arm's obligations (`guard_int_arm_obligations`) is the
//@ mechanism: switch condition as the walk translated it at the switch, `x % 3 == 0`; the arm reassigns the
//@ mechanism: discriminant local `k`, and the assert reads its new value.
//@ accept-means: an assert that fails on every execution of arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(0)` takes arm 0, sets `k = 1` and the assert panics.
//@ teeth: accepted if the edge or the goal read the local instead of the value at its site.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: u32) {
    let mut k = x % 3;
    match k {
        0 => {
            k = 1;
            assert!(k == 0);
        }
        _ => {}
    }
}
