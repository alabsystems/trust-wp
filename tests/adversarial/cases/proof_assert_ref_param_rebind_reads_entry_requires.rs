//@ expect: reject
//@ mechanism: a REFERENCE parameter the body re-binds to another reference, then a `proof_assert!` of
//@ mechanism: the pointee's ENTRY value: `x = y; proof_assert!((*x)@ == 0)` under `#[requires((*x)@ == 0)]`,
//@ mechanism: for `x: &mut u32` and for `x: &u32`. The proof_assert lane binds `x` to `y` (`x = y;
//@ mechanism: proof_assert!((*x)@ == (*y)@)` is proved) and reads the precondition, a fact about the entry
//@ mechanism: referent under the same name, beside that binding, so it constrains `*y`. D-140's
//@ mechanism: withdrawal of a re-bound parameter's entry facts reads the substitution of a by-value
//@ mechanism: parameter only and skips every parameter typed `&`, `&mut` or a raw pointer, so these keep
//@ mechanism: their entry facts. Found probing that withdrawal sideways; no drop is involved.
//@ accept-means: a `proof_assert!` is credited from a reference parameter's entry precondition after the
//@ accept-means: body re-bound the parameter to a reference the precondition says nothing about, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at each assertion `*x` is `*y`, which the precondition leaves arbitrary;
//@ WHY THE CONTRACT IS FALSE: `shared_ref_rebind(&0, &5)` asserts `5 == 0`.
//@ fixed-by: D-241: re-binding a reference parameter writes its own storage, which withdraws its entry facts.
//@ teeth: LIVE: each function ACCEPTED, exit 0, `proof_assert in creusot_test::<fn> verified`, on D-140's
//@ teeth: driver and on the campaign driver it branches from.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*x)@ == 0)]
pub fn mut_ref_rebind<'a>(mut x: &'a mut u32, y: &'a mut u32) {
    x = y;
    proof_assert!((*x)@ == 0);
}

#[requires((*x)@ == 0)]
pub fn shared_ref_rebind<'a>(mut x: &'a u32, y: &'a u32) {
    x = y;
    proof_assert!((*x)@ == 0);
}
