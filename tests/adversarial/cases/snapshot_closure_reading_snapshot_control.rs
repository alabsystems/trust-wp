//@ expect: verify
//@ mechanism: a closure written inside `snapshot!` never runs: the capture is kept under
//@ mechanism: `cfg(trust_wp)` and behind `if false` otherwise. The program-context validator walks it
//@ mechanism: at a raised snapshot-capture depth from its enclosing body, but visits it again as a
//@ mechanism: body of its own, where the depth started at zero, so the deref rustc inserts for
//@ mechanism: `mapping[x]` through a `Snapshot` was refused as a run-time panic (should_succeed
//@ mechanism: `such_that.rs`).
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — refused at `mapping` with the closure visited at depth zero, verified once a
//@ teeth: closure inside a snapshot capture starts its own visit inside it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() {
    let mapping = snapshot!(|x: Int| x + 1);
    let predicate = snapshot!(|x: Int| mapping[x] == x + 1);
    proof_assert!(predicate[3]);
}
