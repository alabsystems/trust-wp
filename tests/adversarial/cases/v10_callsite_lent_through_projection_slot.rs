//@ expect: reject
//@ mechanism: `params_lent_into_another_parameter` read an associated-type projection as a type
//@ mechanism: parameter: a slot only when the borrow's region is early-bound. A projection is its
//@ mechanism: normalized type, which the signature does not show: `<() as Tr<'a>>::Slot` IS
//@ mechanism: `Option<&'a mut i32>`, and `'a` is late-bound (it appears only in argument types).
//@ mechanism: So each callee lent `p` into `slot` while its signature recorded no lend, its
//@ mechanism: `^p == *p` (and the pre-Creusot `*p == old(*p)`) was read at every call, and each
//@ mechanism: caller was credited with its argument unchanged after writing 5 through the slot.
//@ accept-means: a caller (or an assertion after the call) is credited with the final value of a
//@ accept-means: borrow it lent into another argument through a projection-typed slot.
//@ WHY THE CONTRACT IS FALSE: every caller writes 5 through the slot the callee stored `x` in, so
//@ WHY THE CONTRACT IS FALSE: `^x` is 5 and the precondition makes the entry `*x` something else;
//@ WHY THE CONTRACT IS FALSE: `stash_proj_assert`'s `*x == before` is false after the same write.
//@ fixed-by: D-108 (a projection naming a region the borrow's region outlives is a slot for it)
//@ teeth: MEASURED (debug driver): f6039647 verifies `stash_proj_caller`,
//@ teeth: `stash_proj_old_caller`, `stash_vec_proj_caller`, `caller_replace`,
//@ teeth: `caller_direct_item`, `method_proj_caller` and `proof_assert in stash_proj_assert`; on
//@ teeth: D-108 every callee clause is refused by name, no caller verifies and the assertion FAILS.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr<'a> {
    type Slot;
    type Item;
}

impl<'a> Tr<'a> for () {
    type Slot = Option<&'a mut i32>;
    type Item = &'a mut i32;
}

#[ensures(^p == *p)]
pub fn stash_proj<'a>(p: &'a mut i32, slot: &mut <() as Tr<'a>>::Slot) {
    *slot = Some(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_proj_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_proj(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(*p == old(*p))]
pub fn stash_proj_old<'a>(p: &'a mut i32, slot: &mut <() as Tr<'a>>::Slot) {
    *slot = Some(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_proj_old_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_proj_old(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(^p == *p)]
pub fn stash_vec_proj<'a>(p: &'a mut i32, v: &mut Vec<<() as Tr<'a>>::Item>) {
    v.push(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_vec_proj_caller(x: &mut i32) {
    let mut v: Vec<&mut i32> = Vec::new();
    stash_vec_proj(x, &mut v);
    if let Some(r) = v.pop() {
        *r = 5;
    }
}

#[ensures(^p == *p)]
pub fn by_replace<'a>(p: &'a mut i32, slot: &mut <() as Tr<'a>>::Slot) {
    let _ = std::mem::replace(slot, Some(p));
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn caller_replace(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    by_replace(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(^p == *p)]
pub fn by_direct_item<'a>(p: &'a mut i32, slot: &mut <() as Tr<'a>>::Item) {
    *slot = p;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn caller_direct_item(x: &mut i32) {
    let mut other = 0i32;
    let mut slot: &mut i32 = &mut other;
    by_direct_item(x, &mut slot);
    *slot = 5;
}

pub struct K;

impl K {
    #[ensures(^p == *p)]
    pub fn stash<'a>(&self, p: &'a mut i32, slot: &mut <() as Tr<'a>>::Slot) {
        *slot = Some(p);
    }
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn method_proj_caller(x: &mut i32) {
    let k = K;
    let mut slot: Option<&mut i32> = None;
    k.stash(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[requires(*x != 5i32)]
pub fn stash_proj_assert(x: &mut i32) {
    let before = *x;
    let mut slot: Option<&mut i32> = None;
    stash_proj(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
    proof_assert!(*x == before);
}
