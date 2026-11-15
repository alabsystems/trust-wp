//@ expect: reject
//@ mechanism: a `&mut` local first bound to `&mut x` and then reassigned by a plain move (`r = p;`) kept its borrow-chain edge to `x` in the proof_assert substitution lane — a move records no edge, and nothing removed the one the first binding left — so the write through the reassigned local was attributed to `x`.
//@ fixed-by: wp-s84 (a whole-local assignment drops the edge the local held; the handlers re-record only what the new value warrants)
//@ accept-means: after `r = p`, a write through `r` is credited to the place `r` was FIRST created on, so `x` is proved changed by a write that went to `*p`.
//@ WHY THE PROGRAM IS WRONG: `r` points at `*p` when `*r = 7` runs; `x` is still 5, and the assertion claims 7.
//@ teeth: LIVE on the campaign tip 684821d0 and on the D1 build d309075a: ACCEPTED, base_exit_code=0
//@ teeth: (z_reassign_param_false.out). With the stale edge
//@ teeth: dropped: FAILED with a counterexample, exit 1 (same probe).
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k(p: &mut i32) {
    let mut x = 5i32;
    let mut r = &mut x;
    r = p;
    *r = 7;
    proof_assert!(x == 7i32);
}
