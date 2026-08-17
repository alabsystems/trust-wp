//@ expect: reject
//@ mechanism: sibling-binder prophecy fusion — store_prophecy_repair repairs the STORED binder but
//@ mechanism: keeps ONE symbol for the sibling's `*first`/`^first`, forcing idx(cur,0)==idx(fin,0)
//@ fixed-by: 932a7de (Fix A) — the audited shape is take_first_mut (memory/final-collapse-audit.md)
//@ accept-means: the sibling binder of a nested `&mut &mut [T]` split was fused into a single
//@ accept-means: symbol, so `^first` and `*first` are the same term. That is the exact
//@ accept-means: z3-adjudicated load-bearing false lemma behind the take_first_mut false accept —
//@ accept-means: an accept here means it is live again, on a contract that is FALSE.
//@ timeout: 300
//@
//@ WHY THE CONTRACT IS FALSE: `take_first_inverted` hands the caller a `&mut T` into the slice.
//@ The caller may write through it, so the returned borrow's final value is not its current value.
//@ (The TRUE contract for this function is take_first_mut's; see a2_sibling_binder_control.)
//@ teeth: ★VERIFIED. Method (ii): Fix A disabled in-tree (deref_collapse R1 binder strip +
//@ teeth: sort_embeds_mut_ref + final_collapse_requires_prophecy + expr_sort_may_embed_mut_ref_syntactic
//@ teeth: + the driver-side sibling refusal), A/B'd in ONE build via an env knob. Result: ACCEPTED —
//@ teeth: trust-wp proves this FALSE contract. The false accept reproduces on demand.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::mem;

#[ensures(match result {
    Some(r) => ^r == *r,
    None => true,
})]
pub fn take_first_inverted<'a, T>(self_: &mut &'a mut [T]) -> Option<&'a mut T> {
    match mem::take(self_).split_first_mut() {
        None => None,
        Some((first, rem)) => {
            *self_ = rem;
            Some(first)
        }
    }
}
