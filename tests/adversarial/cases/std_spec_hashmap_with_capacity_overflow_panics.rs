//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: `HashMap::with_capacity` sizes a hashbrown table for `capacity` entries and panics
//@ mechanism: ("Hash table capacity overflow") when that table's layout does not fit. Its std spec
//@ mechanism: stated no precondition. It now owes a bound on the table, sized by the `(K, V)` slot
//@ mechanism: the call instantiates.
//@ accept-means: `HashMap::with_capacity`'s spec stopped owing its capacity-overflow panic.
//@ fixed-by: D-121 — allocation-sizing std specs owe the byte bound they panic on.
//@ WHY THE CONTRACT IS FALSE: `g` claims to return normally for every `n@ >= 2^60`. A table for
//@ WHY THE CONTRACT IS FALSE: `2^60` entries has at least `2^61` buckets of 16-byte `(u64, u64)`
//@ WHY THE CONTRACT IS FALSE: slots, more than `isize::MAX` bytes, and hashbrown panics sizing it.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_hashmap_with_capacity_in_range_control differs in the `requires`
//@ teeth: bound alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::collections::HashMap;

#[requires(n@ >= 1152921504606846976)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let m: HashMap<u64, u64> = HashMap::with_capacity(n);
    m.len()
}
