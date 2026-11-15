//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so a switch on `PtrMetadata` of a borrow of `*a` demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee. A slice pattern (`match &*a { [_x, _y] => .. }`) switches on exactly that length, so its arms are walked after a write through `a` where the switch used to owe the fail-closed `false`.
//@ mechanism: here the slice has three elements, so the two-element arm is not taken and the result is `3`.
//@ accept-means: the pattern's length switch read a length other than the one the pointer carries.
//@ WHY THE CONTRACT IS FALSE: with `a@.len() == 3` the match falls to `_` and returns `3`, not `2`.
//@ teeth: UNVERIFIED as a gate: `unknown (refutation withheld)` before D-168 (the switch owed the fail-closed `false`), `f FAILED` on `result@ == 2` after. It pins that the admitted length is the pointer's own.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 3)]
#[ensures(result@ == 2)]
pub fn f(a: &mut [u32]) -> u32 {
    a[0] = 1;
    match &*a {
        [_x, _y] => 2,
        _ => 3,
    }
}
