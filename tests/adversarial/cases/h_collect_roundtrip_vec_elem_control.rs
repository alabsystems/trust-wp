//@ expect: verify
//@ mechanism: Iterator::collect spec — the `result@ == self@` view bridge must not reach non-roundtrip collects
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: n/a (control) — this contract is TRUE; it must verify via the gated roundtrip spec.
//@ mechanism: Besides Creusot's `self@ == result@` for `Vec::into_iter` (see
//@ mechanism: h_collect_roundtrip_vec_len_control), the element read needs the result's view to
//@ mechanism: share the components of the value it views (view.rs
//@ mechanism: assert_seq_view_identity_components). With fresh proxies equated to them, ay found
//@ mechanism: the UNSAT but the proof went through a Nelson-Oppen array/offset lemma its strict
//@ mechanism: checker declines, and the verdict was withheld.
//@ teeth: n/a — over-refusal control for the (Self, B) whitelist; h_collect_roundtrip_vec_elem is
//@ teeth: its false twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 2 && v@[1]@ == 7)]
#[ensures(result@.len() == 2 && result@[1]@ == 7)]
pub fn c_elem(v: Vec<u32>) -> Vec<u32> {
    let r: Vec<u32> = v.into_iter().collect();
    r
}
