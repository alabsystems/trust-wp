//@ expect: reject
//@ mechanism: `encode_resolve` read `resolve(w)` of an annotated variable as the by-value `true`
//@ mechanism: when its datatype's declaration embedded no `&mut`. The builtin models declare an
//@ mechanism: `Option<&mut i32>` (or `Result<&mut i32, _>`) field at `Int`, so `W { o: Option<&mut
//@ mechanism: i32> }` read as holding no borrow; declarations are also keyed by bare name and built
//@ mechanism: once per function from the first instantiation met, so no declaration answers for
//@ mechanism: the value at hand. `resolve(w.o)` reached the same declaration through the collapse
//@ mechanism: guard: `^` distributed into the field getter's argument, and `^w` of a by-value `W`
//@ mechanism: collapsed onto `w` because W's declaration embedded no `&mut`, so the claim was
//@ mechanism: `get0(w) == get0(w)`.
//@ accept-means: a by-value struct holding a borrow is credited as resolved at the return although
//@ accept-means: the body wrote through that borrow.
//@ WHY THE CONTRACT IS FALSE: `w`'s borrow has current value != 5 at entry and final value 5 (the
//@ WHY THE CONTRACT IS FALSE: body writes 5 through it before dropping it), so `resolve(w)`, which
//@ WHY THE CONTRACT IS FALSE: states `*p == ^p` of that borrow, is false.
//@ fixed-by: D-126 (`sort_holds_no_borrow` asks the sort's own shape, never a declaration; the
//@ fixed-by: driver marks a declaration whose Rust type may hold a `&mut`, and the collapse guard
//@ fixed-by: reads the mark)
//@ teeth: MEASURED (debug driver, ay 57a37e51): bdbba131 verifies opt_field, res_field,
//@ teeth: opt_field_projected and res_field_projected (ACCEPTED); on D-126 each is refused.
//@ teeth: Before the declaration's mark, `resolve(w.o)` spelled with the trust_wp prelude still
//@ teeth: verified over D-126's `sort_holds_no_borrow`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

pub struct W<'a> {
    pub o: Option<&'a mut i32>,
}

pub struct R<'a> {
    pub r: Result<&'a mut i32, ()>,
}

#[requires(match w.o { Some(p) => *p != 5i32, None => false })]
#[ensures(resolve(w))]
pub fn opt_field(w: W<'_>) {
    if let Some(p) = w.o {
        *p = 5;
    }
}

#[requires(match r.r { Ok(p) => *p != 5i32, Err(_) => false })]
#[ensures(resolve(r))]
pub fn res_field(r: R<'_>) {
    if let Ok(p) = r.r {
        *p = 5;
    }
}

#[requires(match w.o { Some(p) => *p != 5i32, None => false })]
#[ensures(resolve(w.o))]
pub fn opt_field_projected(w: W<'_>) {
    if let Some(p) = w.o {
        *p = 5;
    }
}

#[requires(match r.r { Ok(p) => *p != 5i32, Err(_) => false })]
#[ensures(resolve(r.r))]
pub fn res_field_projected(r: R<'_>) {
    if let Ok(p) = r.r {
        *p = 5;
    }
}
