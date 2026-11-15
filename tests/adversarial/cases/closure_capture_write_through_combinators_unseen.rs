//@ expect: reject
//@ mechanism: a closure that WRITES a host local through a `&mut` it captured, handed to a std
//@ mechanism: combinator. The write happens inside library code no lane walks, and the call lane
//@ mechanism: gives a post-call value only to a top-level `&mut` argument; the closure value that
//@ mechanism: carries the borrow is not one. The host's proof reads the local at its value before
//@ mechanism: the call. One host per spelling: a unique-borrow capture through `Option::map` on a
//@ mechanism: parameter and on a literal `Some`, `unwrap_or_else`, `get_or_insert_with` and
//@ mechanism: `sort_by`, a `move` closure over a `&mut` bound beforehand, and the closure moved into
//@ mechanism: a `Box` first (`Box::new` stores it; `map` runs it).
//@ accept-means: a host is reported `verified` although the closure it hands over sets `c` to 5
//@ accept-means: before the host returns `c`.
//@ WHY THE CONTRACT IS FALSE: each host runs its closure on some input (`o = Some(_)`, `o = None`
//@ WHY THE CONTRACT IS FALSE: for `unwrap_or_else`, a slice of two for `sort_by`) and returns 5.
//@ fixed-by: D-118: a callable that writes through a `&mut` it captures, handed to code trust-wp does
//@ fixed-by: not verify, leaves the host with no credit.
//@ teeth: ACCEPTED, exit 0, every host `verified`, on the binary before D-118. After it each host's
//@ teeth: credit is withdrawn.
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

#[ensures(result@ == 0)]
pub fn via_map(o: Option<u32>) -> u32 {
    let mut c = 0u32;
    let _ = o.map(|_| c = 5);
    c
}

#[ensures(result@ == 0)]
pub fn via_map_on_some() -> u32 {
    let mut c = 0u32;
    let _ = Some(1u32).map(|_| c = 5);
    c
}

#[ensures(result@ == 0)]
pub fn via_unwrap_or_else(o: Option<u32>) -> u32 {
    let mut c = 0u32;
    let _ = o.unwrap_or_else(|| {
        c = 5;
        1
    });
    c
}

#[ensures(result@ == 0)]
pub fn via_get_or_insert_with() -> u32 {
    let mut c = 0u32;
    let mut o: Option<u32> = None;
    let _ = o.get_or_insert_with(|| {
        c = 5;
        1
    });
    c
}

#[ensures(result@ == 0)]
pub fn via_sort_by(v: &mut [u32]) -> u32 {
    let mut n = 0u32;
    v.sort_by(|a, b| {
        n = 5;
        a.cmp(b)
    });
    n
}

#[ensures(result@ == 0)]
pub fn via_moved_mut_ref(o: Option<u32>) -> u32 {
    let mut c = 0u32;
    let r = &mut c;
    let _ = o.map(move |_| *r = 5);
    c
}

#[ensures(result@ == 0)]
pub fn via_box(o: Option<u32>) -> u32 {
    let mut c = 0u32;
    let _ = o.map(Box::new(|_: u32| c = 5));
    c
}
