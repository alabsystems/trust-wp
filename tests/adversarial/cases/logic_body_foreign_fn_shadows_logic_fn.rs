//@ expect: reject
//@ mechanism: a FOREIGN item declared in the owner's body shadows a logic function of the same name
//@ mechanism: for the owner's clauses: rustc resolves `k(x)` in the contract of `g` to the body's
//@ mechanism: `unsafe extern "C" { safe fn k(..); }` (an edition-2024 `safe` item needs no `unsafe`
//@ mechanism: block, so the clause type-checks). D-174's shadowed_by_body_item walks
//@ mechanism: `hir_crate_items().free_items()`; the `extern` block is a free item with no name and
//@ mechanism: its `k` is a foreign item, so nothing withholds the module's `a::k`.
//@ accept-means: the clause's `k` was read as the module's logic fn although it names the body's
//@ accept-means: foreign fn, whose value nothing states.
//@ WHY THE CONTRACT IS FALSE: `k` is an external function about which nothing is known; the
//@ WHY THE CONTRACT IS FALSE: identity `k(x) == x` is the module's logic fn, not this one.
//@ fixed-by: OPEN — committed RED. shadowed_by_body_item must count foreign items too
//@ fixed-by: (`hir_crate_items().foreign_items()` whose block sits in such a body).
//@ mechanism: Here `a::k` is the ONLY logic fn named `k`.
//@ teeth: ACCEPTED (exit 0) both at the review base and at the head it reviewed: D-174 withholds
//@ teeth: the module answer for body items and globs, and a foreign item is neither.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: i64) -> i64 { p }
}
use a::k;

#[ensures(k(x) == x)]
pub fn g(x: i64) {
    unsafe extern "C" {
        safe fn k(p: i64) -> i64;
    }
}
