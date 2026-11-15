//@ expect: reject
//@ mechanism: a callee's precondition holding a raw-pointer cast reaches the call site as clause
//@ mechanism: text, re-parsed there, where the cast is not classified: the obligation must be
//@ mechanism: refused, never dropped. `needs`'s own verification reads the cast at its parameter's
//@ mechanism: type and is true (it has nothing to prove).
//@ fixed-by: D-145
//@ accept-means: an unclassified cast in a callee's precondition is dropped at the call site, and a
//@ accept-means: caller that does not establish it is credited.
//@ WHY THE CONTRACT IS FALSE: `caller(p, q)` with any `q` other than `p`'s address violates
//@ WHY THE CONTRACT IS FALSE: `needs`'s precondition; `caller` owes it and states nothing.
//@ also-verified: needs
//@ teeth: the caller is not verified; before clause casts were parsed the callee's contract was a
//@ teeth: parse error and the call was refused the same way.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p as *const u8 == q)]
pub fn needs(p: *const [u8], q: *const u8) {}

pub fn caller(p: *const [u8], q: *const u8) {
    needs(p, q)
}
