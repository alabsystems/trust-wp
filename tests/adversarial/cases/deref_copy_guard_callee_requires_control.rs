//@ expect: verify
//@ mechanism: control for the frozen-memory guard of D-118: a contract-free body copies `*x` out of a
//@ mechanism: SHARED reference and calls `needs_nonzero` under `copy != 0`. The guard reads through a
//@ mechanism: dereference, which `guard_reads_only_immutable_locals` refuses (an arm could store
//@ mechanism: through it), so the call's precondition was stated UNGUARDED and the body refuted.
//@ mechanism: No statement here writes through `x`, nothing reachable from it is interior-mutable,
//@ mechanism: and `x` is not `&mut`: the guard reads the value the obligation reads.
//@ accept-means: n/a (control) — the call is guarded.
//@ fixed-by: n/a (control)
//@ teeth: control — `hop verified`. Refuted (`hop FAILED`, unguarded `*x@ != 0`) on the binary
//@ teeth: before D-118. Its twin deref_copy_guard_callee_requires_off_by_one is refuted.
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

pub fn hop(x: &u32) -> u32 {
    let x = *x;
    if x != 0 { needs_nonzero(x) } else { 0 }
}
