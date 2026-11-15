//@ expect: reject
//@ mechanism: `synthesize_indexed_write_postconditions` (callbacks/indexed_write_synthesis.rs) turns every
//@ mechanism: `(*param)[idx] = val` the mut-borrow extractor records into the PREMISE `(^param)@[idx] == val`
//@ mechanism: of the function VC, with no guard: the path that performs the write is not consulted. The
//@ mechanism: final value the mut-borrow lane computes is right, `Ite(flag, (*a)@.set(i, 3), *a)` (traced),
//@ mechanism: but the premise states the write on every path, so where `flag` is false it asserts
//@ mechanism: `(^a)@[i] == 3` while `^a` is the entry value, and the postcondition is proved from it.
//@ mechanism: the array spelling: `&mut [u32; 2]` has a constant length, so its bounds check was admitted
//@ mechanism: before wp-s120's slice bounds reading, and this hole is not that change's.
//@ accept-means: a function that writes `a[0]` only when `flag` holds is verified against a final value that
//@ accept-means: holds 3 at index 0 on every path, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `g(&mut [0, 0], false)` writes nothing, so `(^a)[0]` is 0.
//@ teeth: ACCEPTED at the campaign tip, and with wp-s120's slice bounds reading: the premise is synthesized for every indexed write, whatever the
//@ teeth: pointer type.
//@ teeth: Rejected with D-169.
//@ fixed-by: D-169 (the point-write facts are read off the lane's final value path by path, each under its path's conditions).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((^a)[0]@ == 3)]
pub fn g(a: &mut [u32; 2], flag: bool) {
    if flag {
        a[0] = 3;
    }
}
