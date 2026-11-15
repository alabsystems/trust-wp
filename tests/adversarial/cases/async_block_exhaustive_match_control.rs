//@ expect: verify
//@ mechanism: over-refusal control for D-117: an exhaustive `match` in an async block leaves a MIR `Unreachable` on the discriminant switch's otherwise edge. rustc's exhaustiveness check proved that edge dead, and it owes nothing here as it owes nothing in a program fn (`body_reaches_diverging_call`), so the block is not refused.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — the block owes nothing; a refusal here means a proved-dead edge is read as an obligation.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == o)]
pub fn f(o: Option<u32>) -> Option<u32> {
    let _fut = async move {
        match o {
            Some(v) => v,
            None => 0,
        }
    };
    o
}
