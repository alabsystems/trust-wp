//@ expect: reject
//@ mechanism: a loop invariant calls `k()`, and the function binds a local `k`, a closure returning 0,
//@ mechanism: before the loop; the crate root declares a logic function `k` returning 10. The invariant
//@ mechanism: is resolved where it is written, inside the body, where the local shadows every item, so
//@ mechanism: Rust reads `k()` as a call of the local closure and `k() == 10` is false. The resolver
//@ mechanism: resolves an invariant in the scope of its function's MODULE, never consulting the body's
//@ mechanism: bindings, reads the root's logic function, and credits the loop with an invariant false
//@ mechanism: on entry.
//@ fixed-by: D-195 — REFUSED: a loop clause stands inside the owner's body, and a binding of the name
//@ fixed-by: anywhere in that body may be the local in scope at the loop, so the lookup refuses
//@ fixed-by: (`block_scope::local_may_shadow`, `ClausePosition::Body`) and the call is left unresolved
//@ fixed-by: and the encoder refuses the clause. A `requires`/`ensures` stands before every local and
//@ fixed-by: is not refused.
//@ accept-means: `host` is credited with the invariant `k() == 10`, which Rust evaluates with the local
//@ accept-means: `k` (0), and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host verified ✓ (loop invariant + call obligations)`). With
//@ teeth: D-195: `unknown` (`host error: ... `k` names one of several definitions`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> u32 {
    pearlite! { 10u32 }
}

pub fn host() -> u32 {
    let k = || 0u32;
    let mut i = 0u32;
    #[invariant(k() == 10u32)]
    while i < 3 {
        i += 1;
    }
    i
}
