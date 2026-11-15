//@ expect: reject
//@ mechanism: `encode_resolve` read `resolve(x)` of an annotated variable as the by-value `true`
//@ mechanism: when `sort_embeds_mut_ref` said its sort holds no borrow. That predicate answers the
//@ mechanism: collapse guard's question, and says `false` of every value-model canonical sort
//@ mechanism: (`Vec` -> Seq; `Rc`/`Snapshot`/.. -> Int), whose annotation no longer carries the
//@ mechanism: element sort: a returned `Vec` of the caller's borrow was read as resolved.
//@ mechanism: `resolve(*s)` of `s = snapshot!(x)` stripped the `*` as if it were a borrow's and read
//@ mechanism: the snapshot variable as a value: `true`.
//@ accept-means: a returned `Vec<&mut i32>` is credited as resolved at the return; a snapshot of a
//@ accept-means: borrow is asserted resolved before the body writes it.
//@ WHY THE CONTRACT IS FALSE: the caller holding the returned `Vec` decides the final value of the
//@ WHY THE CONTRACT IS FALSE: borrow it holds; `*s` is the borrow `x` (entry value != 5), whose
//@ WHY THE CONTRACT IS FALSE: final value is the 5 the body writes.
//@ fixed-by: D-126 (`sort_holds_no_borrow` asks the sort's own shape: a value-model name erased its
//@ fixed-by: element sort; the by-value reading is of the variable itself, never through a stripped
//@ fixed-by: `*`)
//@ teeth: The r11 review measured (ay 0e44aed6a) ret_vec verified on 6a828d52, and with the
//@ teeth: trust_wp prelude `proof_assert in ..::snap_resolve_before verified`.
//@ teeth: MEASURED (debug driver, ay 57a37e51): bdbba131 verifies ret_vec (TEETH LOST:
//@ teeth: snap_resolve_before is unknown in this spelling, and its `&mut bool` twin verifies
//@ teeth: with the trust_wp prelude); on D-126 both are refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[ensures(resolve(result))]
pub fn ret_vec(x: &mut i32) -> Vec<&mut i32> {
    let mut v = Vec::new();
    v.push(x);
    v
}

#[requires(*x != 5i32)]
pub fn snap_resolve_before(x: &mut i32) {
    let s = snapshot!(x);
    proof_assert!(resolve(*s));
    *x = 5;
}
