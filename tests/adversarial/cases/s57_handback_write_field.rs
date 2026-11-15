//@ expect: reject
//@ mechanism: same defect reached through a FIELD projection: the body writes `s.0` and hands back `&mut s.0`. `(*s).0` in an `ensures` is the ENTRY value of that field, `*result` is the returned borrow's current pointee (9), so the claim is false; the returned borrow was named by the same projection the entry state uses, so the equality was discharged without consulting the store.
//@ fixed-by: wp-s57 435abd9b (refusal) + 4da7f19a (narrowed to stores that overlap the returned referent)
//@ accept-means: only a whole-parameter handback is being guarded, so a field reborrow still carries the entry pointee into `result`.
//@ WHY THE PROGRAM IS WRONG: for an entry `s.0 == 0` the returned reference reads 9, so `*result == (*s).0` is 9 == 0.
//@ teeth: A/B'd against a pre-fix build: ACCEPTED (`trust-wp: hb_field_star verified`,
//@ teeth: `base_exit_code=0`) on the wp-campaign ce1d56fc worktree build
//@ teeth: of this same field-reborrow program, rejected here.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S(pub u32, pub u32);

#[ensures(*result == (*s).0)]
pub fn hb_field_star(s: &mut S) -> &mut u32 {
    s.0 = 9;
    &mut s.0
}
