//@ expect: reject
//@ mechanism: the bounds check of closure_index_through_option_map_uncharged through every other
//@ mechanism: closure-taking combinator of `Option`, `Result` and `bool` whose builtin spec states
//@ mechanism: no closure precondition: `and_then`, `unwrap_or_else`, `map_or_else`, `filter`,
//@ mechanism: `is_some_and`, `ok_or_else`, `get_or_insert_with`, `Result::map` and `bool::then`.
//@ mechanism: Each contracted host indexes an unconstrained slice by an unconstrained index inside
//@ mechanism: the closure it hands over; one host per combinator, so a credit on any one of them is
//@ mechanism: the hole reopening for that combinator.
//@ accept-means: a host is reported `verified` although calling it with an empty slice panics with
//@ accept-means: "index out of bounds" inside the closure the combinator runs.
//@ fixed-by: D-118
//@ teeth: on the binary before D-118 every host here but `via_bool_then` is `verified`, the
//@ teeth: per-function gate's false credit, and each combinator measured alone in its own crate
//@ teeth: ACCEPTED at exit 0. `via_bool_then` is `unknown` there on its own lane (a fail-closed
//@ teeth: `false` for a construct trust-wp cannot model), so `bool::then` carries no teeth today and
//@ teeth: is kept for the day its spec is modelled. After D-118 each closure is a target that is not
//@ teeth: verified and each host's credit is withdrawn.
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
pub fn via_and_then(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.and_then(|j| Some(w[j]));
    1
}

#[ensures(result@ == 1)]
pub fn via_unwrap_or_else(o: Option<u32>, w: &[u32], k: usize) -> u32 {
    let _ = o.unwrap_or_else(|| w[k]);
    1
}

#[ensures(result@ == 1)]
pub fn via_map_or_else(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.map_or_else(|| 0, |j| w[j]);
    1
}

#[ensures(result@ == 1)]
pub fn via_filter(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.filter(|j| w[*j] == 0);
    1
}

#[ensures(result@ == 1)]
pub fn via_is_some_and(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.is_some_and(|j| w[j] == 0);
    1
}

#[ensures(result@ == 1)]
pub fn via_ok_or_else(o: Option<u32>, w: &[u32], k: usize) -> u32 {
    let _ = o.ok_or_else(|| w[k]);
    1
}

#[ensures(result@ == 1)]
pub fn via_get_or_insert_with(o: &mut Option<u32>, w: &[u32], k: usize) -> u32 {
    let _ = o.get_or_insert_with(|| w[k]);
    1
}

#[ensures(result@ == 1)]
pub fn via_result_map(o: Result<usize, u32>, w: &[u32]) -> u32 {
    let _ = o.map(|j| w[j]);
    1
}

#[ensures(result@ == 1)]
pub fn via_bool_then(b: bool, w: &[u32], k: usize) -> u32 {
    let _ = b.then(|| w[k]);
    1
}
