//@ expect: verify
//@ mechanism: the twin of post_loop_walk_shared_reborrow_of_ref_carrying_type_control: `out.len()` lends
//@ mechanism: a local `Vec<&T>` by a shared auto-borrow after the loop, and the lent-locals scan asked
//@ mechanism: the bare `is_freeze` query about a type that carries a region variable.
//@ accept-means: n/a (control) — `count` returns `n`.
//@ teeth: control — `count panicked during verification: region variables should not be hashed` when
//@ teeth: the scan asks the bare query; `count verified` when it asks the region-erasing one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == n@)]
pub fn count<T>(s: &Vec<T>, n: u32) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let out: Vec<&T> = Vec::new();
    let _l = out.len();
    let _ = s;
    i
}
