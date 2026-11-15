//@ expect: reject
//@ mechanism: an `exists` binder written with a machine-integer type (`exists<x: u32>`) ranges over
//@ mechanism: that type's values in the pinned oracle; trust-wp-core reads the binder over the
//@ mechanism: unbounded `Int` (contract_parser::WrittenTypeSite::QuantifierBinder), so a witness
//@ mechanism: outside the type proves an existential no value of the type satisfies.
//@ accept-means: a machine-integer quantifier binder ranged over values its type does not have.
//@ WHY THE CONTRACT IS FALSE: every u32 has a view at least 0, so no x satisfies `x@ < 0`.
//@ fixed-by: D-203 — a machine-integer binder ranges over its type's values, so the existential
//@ fixed-by: has no witness and is refuted. D-232 alone reads the clause's operators at their type
//@ fixed-by: and leaves the binder's range open (D-233).
//@ teeth: ACCEPTED at exit 0 when written: the defect is live. Found probing sideways from D-135
//@ teeth: item 3's machine-integer arithmetic.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(exists<x: u32> x@ < 0)]
pub fn exists_negative_u32() {}
