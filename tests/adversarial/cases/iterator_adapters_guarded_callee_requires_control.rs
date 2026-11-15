//@ expect: verify
//@ mechanism: the isolating control for closure_callee_requires_through_iterator_adapters_uncharged:
//@ mechanism: the SAME hosts and adapters, each closure guarding its `needs_nonzero` call by
//@ mechanism: `x != 0`. Each closure is a target under `requires true` and verifies. The guard is a copy through the `&x` pattern and the closures run in the
//@ mechanism: `FnMut` lane: this pair exercises the frozen-memory guard and the view of a shared
//@ mechanism: dereference D-118 needed for them to verify.
//@ accept-means: n/a (control) — no call leaves `needs_nonzero`'s precondition.
//@ fixed-by: n/a (control)
//@ teeth: control — every closure verifies (the hosts carry no contract, as in the RED twin). Its
//@ teeth: RED twin differs only in the guards.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

pub fn via_for_each(v: &[u32]) -> u32 {
    v.iter().for_each(|&x| {
        if x != 0 {
            needs_nonzero(x);
        }
    });
    1
}

pub fn via_any(v: &[u32]) -> u32 {
    let _ = v.iter().any(|&x| x != 0 && needs_nonzero(x) == 1);
    1
}

pub fn via_all(v: &[u32]) -> u32 {
    let _ = v.iter().all(|&x| x == 0 || needs_nonzero(x) == 1);
    1
}

pub fn via_position(v: &[u32]) -> u32 {
    let _ = v.iter().position(|&x| x != 0 && needs_nonzero(x) == 1);
    1
}
