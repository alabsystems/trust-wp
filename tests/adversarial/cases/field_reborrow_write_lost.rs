//@ expect: reject
//@ mechanism: a borrow of a struct FIELD (`let r = &mut s.a;`) written directly through, with no move and no reassignment anywhere in the body: the write is not carried back to `s.a`, so the field keeps its entry value. The projection in the borrowed place, not any handover of the borrow, is what the write-back lane fails to follow — the simplest shape in this family.
//@ fixed-by: 7bb3a696 — the resolver answers with a base local plus a FIELD PATH, which the edge map's bare-local value has no room for.
//@ accept-means: any write through a borrow of a field is invisible to a later read of that field, with no ghost code, no move and no reassignment needed to trigger it.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` sets `s.a` to 7, and the assertion claims 5.
//@ teeth: CLOSED in the adversarial direction: the case rejects. Its control is still `xfail` — the true twin of the field write is not provable yet — so this pair still records an incompleteness, just no longer a false accept.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct S {
    pub a: i32,
    pub b: i32,
}

pub fn k() {
    let mut s = S { a: 5, b: 6 };
    let r = &mut s.a;
    *r = 7;
    proof_assert!(s.a == 5i32);
}
