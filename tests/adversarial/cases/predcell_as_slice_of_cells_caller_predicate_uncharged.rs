//@ expect: reject
//@ mechanism: `PredCell::as_slice_of_cells(_pred)` grants each element cell the predicate `_pred[i]`,
//@ mechanism: and `_pred` is the caller's own snapshot. Creusot requires it to agree with the slice
//@ mechanism: cell's predicate; trust-wp's cell builtin owed nothing, so a caller may name any
//@ mechanism: element predicate and `get` then returns a value that satisfies it.
//@ accept-means: a PredCell builtin grants a predicate the caller chose, unrelated to the cell.
//@ accept-means: `f()` returns 0, not 42: the element cell holds `a[0]`, which is 0 (stock rustc).
//@ fixed-by: D-138 — the grant is owed as the fail-closed `false`: a slice cell has no view a
//@ fixed-by: contract can state, so Creusot's precondition has nothing to be stated over.
//@ teeth: UNVERIFIED — `unknown (timeout)` on the binary before D-138, where nothing was owed;
//@ teeth: rejected by the fail-closed `false` under it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{cell::PredCell, logic::Mapping, prelude::*};

#[ensures(result@ == 42)]
pub fn f() -> u32 {
    let mut a = [0u32, 1u32];
    let cell = PredCell::from_mut(&mut a[..], snapshot!(|_s: &[u32]| true));
    let preds: Snapshot<Seq<Mapping<u32, bool>>> = snapshot! {
        let p0 = |z: u32| z@ == 42;
        let p1 = |z: u32| z@ == 42;
        seq!(p0, p1)
    };
    let slice = cell.as_slice_of_cells(preds);
    slice[0].get()
}
