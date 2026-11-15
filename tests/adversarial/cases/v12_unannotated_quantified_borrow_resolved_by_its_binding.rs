//@ expect: reject
//@ mechanism: The contract parser gives a quantifier's binder no sort when its type is a tuple, a
//@ mechanism: named generic other than `Vec`, or a `&mut` of a named type (`(&mut i32, i32)`,
//@ mechanism: `Option<&mut i32>`, `&mut Holder`), and the wrapper's binder arm kept the legacy collapse
//@ mechanism: of `^q` onto an unannotated binder, which the formal and closure-state lanes read:
//@ mechanism: `^q == *q` and `resolve(q)` are `q == q`, true of every value the binder ranges over.
//@ accept-means: a claim that every such value's borrow is resolved is credited.
//@ WHY THE CONTRACT IS FALSE: a borrow whose final value differs from its current value exists, so
//@ WHY THE CONTRACT IS FALSE: a tuple and an `Option` holding one exist too, and so does a `&mut Holder`.
//@ fixed-by: D-127 (the final value of a binder a written `forall`/`exists` binds is refused unless
//@ fixed-by: its annotation certifies a sort holding no borrow; D-126 left the unannotated binder
//@ fixed-by: collapsed)
//@ teeth: MEASURED (debug driver): before D-127 none_unresolved_tuple, none_unresolved_option and
//@ teeth: none_moved_struct verified (ACCEPTED); D-127 refuses each.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

pub struct Holder {
    pub v: i32,
}

#[ensures(!(exists<q: (&mut i32, i32)> !resolve(q)))]
pub fn none_unresolved_tuple() {}

#[ensures(!(exists<q: Option<&mut i32>> !resolve(q)))]
pub fn none_unresolved_option() {}

#[ensures(!(exists<q: &mut Holder> ^q != *q))]
pub fn none_moved_struct() {}
