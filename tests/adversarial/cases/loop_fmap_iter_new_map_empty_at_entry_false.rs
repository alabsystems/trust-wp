//@ expect: reject
//@ mechanism: reject twin of loop_fmap_iter_new_map_empty_at_entry_control: `result.get(k) == Some(v)`
//@ mechanism: for every `k` and `v` is FALSE at entry, where `result` is empty and nothing is produced.
//@ mechanism: Stating the facts about `result` in the initialization VC must not cost the refutation.
//@ accept-means: `result` is `FMap::new()`, so `result.get(k)` is `None` at every key when the loop
//@ accept-means: starts, and trust-wp proved `result.get(k) == Some(v)` there.
//@ verdict: failed
//@ fn-failed: empty_at_entry
//@ teeth: not a false-accept gate: refuted `failed` before and since D-227. It pins that the
//@ teeth: facts which make the control's initialization provable leave a genuine refutation standing.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

#[check(ghost)]
pub fn empty_at_entry<K: Eq + std::hash::Hash, V>(m: Ghost<FMap<K, V>>) {
    ghost! {
        let result = FMap::<K, V>::new().into_inner();
        #[invariant(forall<k, v> result.get(k) == Some(v) || produced.len() > 0)]
        for (k, v) in m.into_inner() {}
    };
}
