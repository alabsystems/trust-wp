//@ expect: reject
//@ also-verified: host
//@ mechanism: a closure's contract calls `k()`, and the enclosing function binds a local `k`, a closure
//@ mechanism: returning 0; the crate root declares a logic function `k` returning 10. A closure's
//@ mechanism: contract is resolved inside the enclosing body, where the local shadows every item, so
//@ mechanism: Rust reads `k()` as a call of the local closure (a program function, which Pearlite
//@ mechanism: cannot call). The resolver never consults the enclosing body's bindings: it looks `k` up
//@ mechanism: among the children of the closure's MODULE and reads the root's logic function, so the
//@ mechanism: closure, which returns 10, is credited against a contract whose `k()` Rust evaluates to
//@ mechanism: 0. `host` claims nothing, so its credit is true.
//@ fixed-by: D-195 — REFUSED: a closure's clauses are resolved inside the body that encloses the
//@ fixed-by: closure, and a binding of the name anywhere in that body may be the local in scope, so the
//@ fixed-by: lookup refuses (`block_scope::local_may_shadow`) and the call is left unresolved and the
//@ fixed-by: encoder refuses the clause.
//@ accept-means: the closure claims `result == k()` with Rust's `k` the local closure (0), returns 10,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::{closure#2} verified ✓`). With D-195: `unknown`
//@ teeth: (`host::{closure#2} error: ... `k` names one of several definitions`).
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
    let c = #[ensures(result == k())]
    || -> u32 { 10 };
    c()
}
