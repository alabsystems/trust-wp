//@ expect: verify
//@ xfail: initialization is proved with a proof step ay's strict certificate check does not accept
//@ xfail: (`proof-trusted`), and preservation is withheld (the modified-variable scan counts `result`
//@ xfail: as written by the loop), so the verdict is `unknown`.
//@ xfail-verdict: unknown
//@ mechanism: control: the contains spelling of loop_fmap_iter_new_map_empty_at_entry_control. The
//@ mechanism: initialization VC substitutes `result`'s binding `fmap_empty()` into the invariant; the
//@ mechanism: only facts saying the map holds no key are stated of `result`'s call, and `fmap_empty`'s
//@ mechanism: own axioms ride on `fmap_insert`, absent here. A validated `FAILED (loop invariant)` at
//@ mechanism: initialization before D-227.
//@ teeth: n/a — control. Its twin loop_entry_binding_facts_new_map_holds_no_key_false.rs is refuted.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

#[check(ghost)]
pub fn no_key<K: Eq + std::hash::Hash, V>(m: Ghost<FMap<K, V>>) {
    ghost! {
        let result = FMap::<K, V>::new().into_inner();
        #[invariant(forall<k> !result.contains(k))]
        for (k, v) in m.into_inner() {}
    };
}
