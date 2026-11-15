//@ expect: reject
//@ verdict: error
//@ refused-with: cannot dereference a ghost value in program context
//@ mechanism: the program-context validator walks the arguments of a `Snapshot::capture` call at a
//@ mechanism: raised snapshot-capture depth, where a ghost deref is not refused, and D-133 item 7
//@ mechanism: trusts a closure written inside such a call when the call's span is `from_expansion`.
//@ mechanism: Any macro's expansion is `from_expansion`: a `macro_rules!` of the user's that wraps its
//@ mechanism: argument in `Snapshot::capture(&..)` writes a capture that runs in every build, unlike
//@ mechanism: `snapshot!`'s, which sits under `cfg(trust_wp)`. `direct` dereferences the ghost in the
//@ mechanism: macro's argument, `closure` in a closure called there; each runs
//@ mechanism: `<Ghost<i32> as Deref>::deref`, which panics, while the verifier reads the ghost's value.
//@ accept-means: program bodies that dereference a ghost at run time inside a capture a user macro wrote
//@ accept-means: are reported verified and the crate exits 0.
//@ fixed-by: D-193: a capture raises the depth only where trust-wp's `snapshot!` expansion wrote it,
//@ fixed-by: for the enclosing walk and for a closure's own visit alike.
//@ WHY THE CONTRACT IS FALSE: each function panics on every call ("Ghost deref called at runtime").
//@ teeth: ACCEPTED (both verified, exit 0) at the campaign base 6e6bf5f3. Natively, built against
//@ teeth: trust-wp-std, each function panics at `*g`. Refused at wp-s150;
//@ teeth: snapshot_macro_capture_reads_ghost_control verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! cap {
    ($e:expr) => {
        Snapshot::capture(&$e)
    };
}

#[ensures(result == 7i32)]
pub fn direct() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = cap!(*g);
    7
}

#[ensures(result == 7i32)]
pub fn closure() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let _s = cap!((|| *g)());
    7
}
