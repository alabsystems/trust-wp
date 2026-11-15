//@ expect: reject
//@ mechanism: the no-pointer twin of v8_callsite_lent_into_raw_pointer: `mut_borrow::lent`'s
//@ mechanism: `may_carry_borrow` answers true past its depth bound, which a recursive type
//@ mechanism: (`Tag` holds `Option<Box<Tag>>`) reaches, so `p` is lent into the `Tag` built from
//@ mechanism: `*p`; the call saw no region in `Tag` and read the pre-Creusot `*p` as `^p`.
//@ accept-means: a caller is credited with a reading of a callee clause its lane did not prove.
//@ WHY THE CONTRACT IS FALSE: `tag` stores 5 through the borrow of `x`, so `^x` is 5 and the
//@ WHY THE CONTRACT IS FALSE: precondition makes the entry `*x` something else.
//@ fixed-by: D-102
//@ teeth: MEASURED on cbadb52d (debug driver): `tag_caller verified`; d454c1e1: unknown. On the
//@ teeth: D-102 tree: tag refused, caller unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct Tag {
    pub id: i32,
    pub next: Option<Box<Tag>>,
}

#[ensures(*p == old(*p))]
pub fn tag(p: &mut i32) -> Tag {
    *p = 5;
    Tag { id: *p, next: None }
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn tag_caller(x: &mut i32) {
    let _ = tag(x);
}
