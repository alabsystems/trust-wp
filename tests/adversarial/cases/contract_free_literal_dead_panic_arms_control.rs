//@ expect: verify
//@ mechanism: the clause-free cap (`unchecked_panic_sites`) skips a switch edge only when EVERY walk visit of the switch stated the edge unreachable as a goal of the verified VC (`ProvedDeadEdges`, D-142: recorded by the lane that pushed the goal, only where `primary_arithmetic_is_exact`).
//@ mechanism: control: every panic arm here is statically dead. The dead arm of a literal switch owes the ordinary goal (`!false` / `true`), which charges it; before, the literal switch stated nothing for either arm and the cap labelled the dead panic calls.
//@ accept-means: n/a (control)
//@ teeth: capped at `unknown (partial: panic paths unchecked (panic call))` without the credit.
//@ fixed-by: D-142 — the switch lanes record the edges their charges prove dead, and the clause-free cap does not walk them
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(x: u32) -> u32 {
    if false {
        panic!()
    }
    let b = false;
    if b {
        unreachable!()
    }
    assert!(true);
    assert!(!false);
    x
}
