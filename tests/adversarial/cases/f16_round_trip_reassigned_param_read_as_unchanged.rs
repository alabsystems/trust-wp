//@ expect: reject
//@ mechanism: D-215 gave `f16` no sort and refused a cast to or from it, but the refusal was the
//@ mechanism: translator returning nothing, and `on_assign_local` then bound the destination to
//@ mechanism: `Var(<source name>)`: `a = (a as f16) as f32` over a parameter `a` was read as the entry
//@ mechanism: `a`, which is the identity reading of the cast the entry sets out to remove. D-169 binds an
//@ mechanism: untranslated assignment to a symbol of its site, and D-217 translates both casts as
//@ mechanism: uninterpreted functions of their operands, which are never their operand.
//@ accept-means: `f16_round_trip(0.1)` returns `0.0999755859375`; an accept claims it returns `0.1`.
//@ fixed-by: D-169 (the site symbol) and D-217 (the casts translated)
//@ teeth: ACCEPTED when committed (`f16_round_trip verified`), and on the campaign tip before D-215, which
//@ teeth: read both casts as the identity; rejected by the merged tip with D-169, and under D-217
//@ teeth: (`f16_round_trip` unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn f16_round_trip(mut a: f32) -> f32 {
    let h = a as f16;
    a = h as f32;
    a
}
