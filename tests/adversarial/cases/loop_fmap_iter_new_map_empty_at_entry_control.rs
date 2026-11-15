//@ expect: verify
//@ xfail: initialization is proved with a proof step ay's strict certificate check does not accept
//@ xfail: (`proof-trusted`), and preservation and the exit time out, so the verdict is `unknown`.
//@ xfail-verdict: unknown
//@ mechanism: control: `result` is `FMap::new()`, empty, so `result.get(k) != Some(v)` holds at loop
//@ mechanism: entry. The initialization VC substitutes the binding `result == fmap_empty()` into the
//@ mechanism: invariant, and the facts that say the map holds no key are stated of `result`'s call
//@ mechanism: (`result == $_call`, `forall k. !$_call.contains(k)`); the slice no longer named
//@ mechanism: `result`, so it left them out, and the model picked a `get` no empty map has. It was a
//@ mechanism: validated `FAILED (loop invariant)` at initialization before D-227, and should_succeed
//@ mechanism: ghost/fmap_iter's `complicated_identity` was refuted there the same way.
//@ teeth: n/a — control. Its twin loop_fmap_iter_new_map_empty_at_entry_false.rs is refuted.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

#[check(ghost)]
pub fn empty_at_entry<K: Eq + std::hash::Hash, V>(m: Ghost<FMap<K, V>>) {
    ghost! {
        let result = FMap::<K, V>::new().into_inner();
        #[invariant(forall<k, v> result.get(k) != Some(v) || produced.len() > 0)]
        for (k, v) in m.into_inner() {}
    };
}
