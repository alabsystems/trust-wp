//@ expect: reject
//@ mechanism: reject twin of loop_entry_binding_facts_new_map_holds_no_key_control, one `!` removed:
//@ mechanism: an empty map does not hold every key, so the invariant is FALSE at entry, and the facts
//@ mechanism: that describe `result` must leave the refutation standing.
//@ accept-means: `result` is `FMap::new()`, empty when the loop starts, and trust-wp proved that it
//@ accept-means: contains every key there.
//@ verdict: failed
//@ fn-failed: no_key
//@ teeth: not a false-accept gate: refuted `failed` before and since D-227. It pins the
//@ teeth: flavour against a rule that would withhold every initialization refutation over a binding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

#[check(ghost)]
pub fn no_key<K: Eq + std::hash::Hash, V>(m: Ghost<FMap<K, V>>) {
    ghost! {
        let result = FMap::<K, V>::new().into_inner();
        #[invariant(forall<k> result.contains(k))]
        for (k, v) in m.into_inner() {}
    };
}
