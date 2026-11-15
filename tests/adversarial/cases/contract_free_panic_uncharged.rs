//@ expect: reject
//@ mechanism: a CONTRACT-FREE fn that panics unconditionally. Creusot's `Terminator::Abort` makes
//@ mechanism: "this body is unreachable" a goal; trust-wp's body-entry rule states it, but only
//@ mechanism: inside a body that is a verification target, which a contract-free fn was not.
//@ accept-means: a body every call to which panics was examined by nobody and the crate still
//@ accept-means: reported a clean verification run
//@ fixed-by: the contract-free abort/callee-precondition discovery pass
//@ teeth: verified — ACCEPTED on this branch's parent commit, rejected after the pass lands
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

pub fn hop() {
    panic!("boom")
}
