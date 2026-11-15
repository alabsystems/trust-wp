//@ expect: verify
//@ xfail: `evil_reassigned` is `unknown (refutation withheld: goal set carries a fail-closed
//@ xfail: `false` ...)`, never FAILED: a call through a reassigned fn pointer has no unique
//@ xfail: target, and the walker owes a fail-closed `false` for it whatever the argument. Retire
//@ xfail: this directive when such a call owes the precondition of every target it can reach.
//@ xfail-verdict: unknown
//@ mechanism: the value twin of s62_fnptr_reassigned_unannotated_loop: the identical loop calling
//@ mechanism: `f(1)`, which meets `needs_positive`'s precondition, so the contract is TRUE
//@ mechanism: whichever target `f` holds. The marker the unresolved target owes sits behind the
//@ mechanism: loop's path guard; a model of the guard refutes it, which shows only that the call
//@ mechanism: is reached (D-141, a guarded marker is a marker). `xfail-verdict: unknown` keeps
//@ mechanism: that model from being printed as a counterexample to this program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x > 0u32)]
#[ensures(result == x)]
pub fn needs_positive(x: u32) -> u32 {
    x
}

pub fn other(x: u32) -> u32 {
    x
}

#[ensures(result == 7u32)]
pub fn evil_reassigned(c: bool) -> u32 {
    let mut f: fn(u32) -> u32 = other;
    if c {
        f = needs_positive;
    }
    let mut i = 0u32;
    while i < 1u32 {
        let _unused = f(1u32);
        i += 1u32;
    }
    7u32
}
