//@ expect: verify
//@ mechanism: control for the post-loop return walk's lent-locals scan (`mutably_lent_locals`), which asks
//@ mechanism: whether a shared borrow's place type is `Freeze`. `&*v` lends a `Vec<&u32>`, whose type read
//@ mechanism: from borrow-checked MIR carries region variables, and the bare `is_freeze` query hashes
//@ mechanism: its key, which rustc refuses for a region variable: the function panicked during
//@ mechanism: verification (should_succeed ghost/seq_iter.rs `reverse_ghost_ref` was the first seen).
//@ mechanism: Twin: post_loop_walk_shared_borrow_of_generic_ref_vec_control.
//@ accept-means: n/a (control) — `count` returns `n`.
//@ teeth: control — `count panicked during verification: region variables should not be hashed` when
//@ teeth: the scan asks the bare query; `count verified` when it asks the region-erasing one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == n@)]
pub fn count(v: &Vec<&u32>, n: u32) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let w: &Vec<&u32> = &*v;
    let _l = w.len();
    i
}
