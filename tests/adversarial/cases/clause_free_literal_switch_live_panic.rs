//@ expect: reject
//@ mechanism: D-142 reads the edge a value-stable literal discriminant never selects as dead, and
//@ mechanism: only that edge. `c` is the literal `false`, so the edge into `unreachable!()` is the
//@ mechanism: one the literal DOES select: it must stay live, and the cap must still count the
//@ mechanism: panic call. Recording the selected edge instead of the other would credit this body.
//@ accept-means: the literal rule marked the selected edge dead and a body that panics on every
//@ accept-means: call was credited `verified`.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; every call of
//@ WHY THE CONTRACT IS FALSE: `hop` reaches `unreachable!()`.
//@ verdict: error
//@ refused-with: hop vacuous (contradictory premises)
//@ teeth: UNVERIFIED for the cap — the selected edge leaves the literal `false` as the walk's
//@ teeth: returning-path premise, and the vacuity check refuses the body before the cap reads it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop() -> u32 {
    let c = false;
    if c { 1 } else { unreachable!() }
}
