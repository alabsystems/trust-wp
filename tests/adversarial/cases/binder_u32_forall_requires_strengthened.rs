//@ expect: reject
//@ mechanism: a `forall` binder written with a machine-integer type in a PRECONDITION. Read over
//@ mechanism: the unbounded `Int` (contract_parser::WrittenTypeSite::QuantifierBinder) the premise
//@ mechanism: is stronger than the oracle's, whose binder ranges over u32: `forall<x: u32> x@ >= 0
//@ mechanism: || b` holds of every u32 whatever `b` is, but over `Int` (x = -1) it forces `b`.
//@ accept-means: a machine-integer quantifier binder in a premise ranged over values its type does
//@ accept-means: not have, so the function was verified under a precondition its callers never owe.
//@ WHY THE CONTRACT IS FALSE: b = false meets the precondition (every u32 view is at least 0), and
//@ WHY THE CONTRACT IS FALSE: the postcondition `b` is then false.
//@ teeth: rejected `unknown` when written, so the case pins the shape and its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(forall<x: u32> x@ >= 0 || b)]
#[ensures(b)]
pub fn forall_requires_strengthened(b: bool) {}
