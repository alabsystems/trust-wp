//@ expect: reject
//@ mechanism: the same laundering as `contract_free_local_requires_uncharged`, with the
//@ mechanism: precondition coming from a spec for a FOREIGN callee (`Vec::remove` requires the
//@ mechanism: index in bounds) rather than a local `#[requires]`. The callee identity carries no
//@ mechanism: attribute of its own, so the discovery predicate has to consult the spec tables or
//@ mechanism: this half of the hole stays open while the local half closes.
//@ accept-means: a std precondition was laundered by putting the call in a function with no contract
//@ fixed-by: the contract-free abort/callee-precondition discovery pass
//@ teeth: verified — ACCEPTED both on this branch's parent commit AND on the local-callee-only
//@ teeth: version of the pass; rejected once the predicate reads the spec tables
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

// `remove(0)` on an empty vector panics.
pub fn hop(v: &mut Vec<u32>) {
    let _ = v.remove(0);
}
