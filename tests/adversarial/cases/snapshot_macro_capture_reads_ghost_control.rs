//@ expect: verify
//@ mechanism: the TRUE twin of snapshot_capture_spelled_in_program_context_runs_ghost_deref and
//@ mechanism: snapshot_capture_in_user_macro_runs_ghost_deref: the ghost deref sits in the three shapes
//@ mechanism: `snapshot!` itself writes (a `Snapshot::capture` call, the statement form ending in
//@ mechanism: `new_phantom()`, the dispatch form ending in `snapshot_capture_select(..).capture()`),
//@ mechanism: which the macro keeps under `cfg(trust_wp)` and behind `if false` otherwise, so none
//@ mechanism: runs. A capture is trusted by the span of trust-wp's expansion, and each of these carries it.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified with every capture trusted by its spelling, and with only the macro's
//@ teeth: expansion trusted.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7i32)]
pub fn capture_call() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let s = snapshot!(*g + 1i32);
    proof_assert!(*s == 6i32);
    7
}

#[ensures(result == 7i32)]
pub fn statement_form() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = snapshot! {
        let _v = *g;
    };
    7
}

#[ensures(result == 7i32)]
pub fn dispatch_form() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let s = snapshot!(*g);
    proof_assert!(*s == 5i32);
    7
}
