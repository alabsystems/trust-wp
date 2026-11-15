//@ expect: verify
//@ xfail: ay computes UNSAT and withholds it (`unknown (proof-trusted)`: the terminal derivation
//@ xfail: chain is not trust-free), stable in three runs at D-116. It verified while the spec's
//@ xfail: `None` arm was `false`, which let the proof never open that arm; that arm is the one
//@ xfail: D-116 had to make true, so this is the coverage it paid.
//@ mechanism: a `Some` that `Instant::checked_add` returns is exactly `duration` later than the
//@ mechanism: receiver, so a positive duration yields a later instant. D-116 keeps the `Some` arm of
//@ mechanism: the spec as it was and changes only the `None` arm.
//@ accept-means: n/a (control) — the contract is TRUE for every clock reading.
//@ fixed-by: D-116
//@ teeth: verified before D-116, `unknown (proof-trusted)` after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn some_is_later() -> bool {
    let i = Instant::now();
    match i.checked_add(Duration::from_secs(3)) {
        Some(j) => j > i,
        None => true,
    }
}
