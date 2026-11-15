//@ expect: reject
//@ mechanism: `synthesize_indexed_write_postconditions` (callbacks/indexed_write_synthesis.rs) turns every
//@ mechanism: `(*param)[idx] = val` the mut-borrow extractor records into the PREMISE `(^param)@[idx] == val`
//@ mechanism: of the function VC, with no guard: the path that performs the write is not consulted.
//@ mechanism: the slice spelling that predates wp-s120's slice bounds reading: the writing arm is excluded by the precondition and
//@ mechanism: panics, so the fail-closed `false` its bounds check owes at the campaign tip is guarded by `flag`
//@ mechanism: and discharged by `requires(!flag)`, and the unguarded premise proves the postcondition.
//@ accept-means: a function that never writes `a[0]` is verified against a final value that holds 3 there,
//@ accept-means: and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `g(&mut [0, 0], false)` writes nothing, so `(^a)[0]` is 0.
//@ teeth: ACCEPTED at the campaign tip, and with wp-s120's slice bounds reading.
//@ teeth: Rejected with D-169.
//@ fixed-by: D-169 (the point-write facts are read off the lane's final value path by path, each under its path's conditions).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 2 && !flag)]
#[ensures((^a)[0]@ == 3)]
pub fn g(a: &mut [u32], flag: bool) {
    if flag {
        a[0] = 3;
        panic!()
    }
}
