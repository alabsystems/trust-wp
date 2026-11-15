//@ expect: reject
//@ mechanism: the bounds check of closure_index_through_option_map_uncharged through the
//@ mechanism: closure-taking methods of slices and `Vec`: `sort_by_key`, `sort_by`, `retain` and
//@ mechanism: `binary_search_by`. Each contracted host indexes an unconstrained slice by an element
//@ mechanism: of another inside the closure it hands over; one host per method.
//@ accept-means: a host is reported `verified` although calling it with `v = [5, 6]` and an empty
//@ accept-means: `w` panics with "index out of bounds" inside the closure the method runs.
//@ fixed-by: D-118
//@ teeth: ACCEPTED, exit 0, every host `verified`, on the binary before D-118. After it each
//@ teeth: closure is a target that is not verified and each host's credit is withdrawn.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

#[ensures(result@ == 1)]
pub fn via_sort_by_key(v: &mut [usize], w: &[u32]) -> u32 {
    v.sort_by_key(|&j| w[j]);
    1
}

#[ensures(result@ == 1)]
pub fn via_sort_by(v: &mut [usize], w: &[u32]) -> u32 {
    v.sort_by(|&a, &b| w[a].cmp(&w[b]));
    1
}

#[ensures(result@ == 1)]
pub fn via_retain(v: &mut Vec<usize>, w: &[u32]) -> u32 {
    v.retain(|&j| w[j] == 0);
    1
}

#[ensures(result@ == 1)]
pub fn via_binary_search_by(v: &[usize], w: &[u32]) -> u32 {
    let _ = v.binary_search_by(|&j| w[j].cmp(&0));
    1
}
