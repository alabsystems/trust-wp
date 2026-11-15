//@ expect: reject
//@ verdict: error
//@ refused-with: cannot dereference a ghost value in program context
//@ mechanism: the program-context validator recognises a snapshot capture by its syntax and walks
//@ mechanism: it at a raised snapshot-capture depth, where a ghost deref is not refused: a call whose
//@ mechanism: path is `Snapshot::capture`, a block whose tail calls `Snapshot::new_phantom()` (the
//@ mechanism: statement-form `snapshot! { .. }`), and a block whose tail is
//@ mechanism: `snapshot_capture_select(..).capture()` (the type-directed dispatch). The macro keeps its
//@ mechanism: captured code under `cfg(trust_wp)`, so it never runs; the same shapes written by hand in
//@ mechanism: program code run in every build. Each function below dereferences a ghost in such a
//@ mechanism: shape: `<Ghost<i32> as Deref>::deref` panics at run time, and the verifier reads it as the
//@ mechanism: ghost's value.
//@ accept-means: program bodies that dereference a ghost at run time inside a hand-written capture
//@ accept-means: call or capture-shaped block are reported verified and the crate exits 0.
//@ fixed-by: D-193: a capture shape raises the depth only where trust-wp's `snapshot!` expansion wrote
//@ fixed-by: it (`ghost::program_context`, the span of a `trust-wp-macros` expansion and the definition
//@ fixed-by: rustc resolved), so each deref here is validated as program code and refused.
//@ WHY THE CONTRACT IS FALSE: each function panics on every call ("Ghost deref called at runtime").
//@ teeth: ACCEPTED (all three verified, exit 0) at the campaign base 4c832882 and at wp-s140 598eed1d.
//@ teeth: Natively each function built against trust-wp-std panics at `*g`. Refused at wp-s150;
//@ teeth: snapshot_macro_capture_reads_ghost_control, the same derefs in the three shapes the macro
//@ teeth: writes, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::SnapshotCaptureFallback, prelude::*};

#[ensures(result == 7i32)]
pub fn capture_call() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = Snapshot::capture(&*g);
    7
}

#[ensures(result == 7i32)]
pub fn new_phantom_tail() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = {
        let _v = *g;
        Snapshot::<()>::new_phantom()
    };
    7
}

#[ensures(result == 7i32)]
pub fn dispatch_tail() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = {
        let _v = *g;
        creusot_std::ghost::snapshot_capture_select(&0i32).capture()
    };
    7
}
