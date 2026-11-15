//@ expect: reject
//@ mechanism: `synthesize_indexed_write_postconditions` (callbacks/indexed_write_synthesis.rs) turns every
//@ mechanism: `(*param)[idx] = val` the mut-borrow extractor records into the PREMISE `(^param)@[idx] == val`
//@ mechanism: of the function VC, with no guard: the path that performs the write is not consulted. The
//@ mechanism: final value the mut-borrow lane computes is right, `Ite(flag, (*a)@.set(i, 3), *a)` (traced),
//@ mechanism: but the premise states the write on every path, so where `flag` is false it asserts
//@ mechanism: `(^a)@[i] == 3` while `^a` is the entry value, and the postcondition is proved from it.
//@ mechanism: here the pointer is a `&mut [u32]`: D-168 lets the bounds check of `a[i]` read the length
//@ mechanism: the pointer carries, where it owed the fail-closed `false`, so the body now reaches the solver.
//@ accept-means: a function that writes `a[i]` only when `flag` holds is verified against a final value that
//@ accept-means: holds 3 at `i` on every path, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `g(&mut [0], 0, false)` writes nothing, so `(^a)[0]` is 0.
//@ teeth: ACCEPTED with D-168; `g FAILED (postcondition)` without it. The array spelling
//@ teeth: indexed_write_on_one_arm_final_value_array.rs is ACCEPTED with and without it, and so is the
//@ teeth: slice spelling whose writing arm the precondition excludes
//@ teeth: (indexed_write_on_precondition_excluded_panicking_arm_final_value_slice.rs): D-168 widens a hole
//@ teeth: that predates it from arms no execution takes to every arm.
//@ teeth: Rejected with D-169.
//@ fixed-by: D-169 (the point-write facts are read off the lane's final value path by path, each under its path's conditions).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(i@ < a@.len())]
#[ensures((^a)[i@]@ == 3)]
pub fn g(a: &mut [u32], i: usize, flag: bool) {
    if flag {
        a[i] = 3;
    }
}
