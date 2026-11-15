//@ expect: reject
//@ mechanism: the goal of an arithmetic panic site is owed by a region walk
//@ mechanism: (`collect_arithmetic_panic_obligations`), never recorded in the CallEffects whose premises it
//@ mechanism: would have to guard: a callee postcondition assumed LATER on the path is guarded only by the
//@ mechanism: obligations recorded so far in its own lane, so it discharges the earlier goal. `below`
//@ mechanism: diverges for `x >= 100`, so its postcondition is true, but it holds only after the addition.
//@ mechanism: the spelling in a function whose loop carries an invariant: its premises come from
//@ mechanism: `collect_call_effects_for_blocks`, whose reaching-obligation guard never sees the region walk's goal.
//@ accept-means: an addition that overflows before the call is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(u32::MAX)` overflows at `x + 1`.
//@ teeth: ACCEPTED at the campaign tip and with D-169.
//@ also-verified: below
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means an obligation another lane owes
//@ fixed-by: guards every premise recorded after its site on the path, as the obligations recorded in the
//@ fixed-by: premise's own lane do (`scope_call_postconditions_under_preconditions`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(true)]
pub fn f(x: u32) -> u32 {
    let y = x + 1;
    below(x);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    y
}
