//@ expect: reject
//@ mechanism: the return lane of the field-borrow shape: a struct field is written through a borrow of it and the whole struct is then returned (`let r = &mut s.a; *r = 7; s`). The return-expression lane binds the returned value to the struct's entry state, the write through the field borrow never reaches it, and the postcondition is discharged against the stale field. Unlike the whole-local move shapes, no handover of the borrow is involved — the projection alone is enough.
//@ fixed-by: 7bb3a696 — the primary lane's `!has_deref` guard now yields to the resolver, so a field written through a borrow of it reaches the returned owner.
//@ accept-means: a function that mutates one of its fields through a borrow and returns the owner is proved to return the pre-mutation value — a false accept in an `#[ensures]` clause, the surface real contracts are written against.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` sets `s.a` to 7 before `s` is returned; `result.a == 5` is false on every run.
//@ teeth: CLOSED. The case now rejects and its control verifies, so the return lane reads the post-write field in both directions.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures(result.a == 5i32)]
pub fn k() -> S {
    let mut s = S { a: 5, b: 6 };
    let r = &mut s.a;
    *r = 7;
    s
}
