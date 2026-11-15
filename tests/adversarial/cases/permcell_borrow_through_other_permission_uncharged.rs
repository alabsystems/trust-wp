//@ expect: reject
//@ mechanism: `PermCell::borrow_mut` and `borrow` take `&self`, so only the permission argument keeps
//@ mechanism: two borrows of one cell apart: Creusot requires `self == perm.ward()` of every access,
//@ mechanism: and the borrow checker then refuses a `&mut` and a `&` of the one permission that guards
//@ mechanism: the cell. trust-wp's PermCell builtins owe nothing about the permission, and the ghost
//@ mechanism: validator's same-origin check reads only a cell bound to a local, so a cell reached
//@ mechanism: through a parameter's field is borrowed mutably under `q`, which guards no cell here,
//@ mechanism: while `r2` still reads it. Each borrow's builtin reads the cell's view at the call,
//@ mechanism: so `*r2` keeps the value read before the write through `r1`.
//@ accept-means: a PermCell access that owes no permission identity lets a body verify that holds a
//@ accept-means: `&mut` and a `&` to one cell at once and reads through the stale one.
//@ accept-means: `f(&mut S { c, p, q })`, with `(c, p) = PermCell::new(1)` and `q` the permission of
//@ accept-means: another `PermCell::new(2)`, returns 1: the write through `r1` is seen through `r2`
//@ accept-means: (run against trust-wp-std's own implementation; the aliasing is undefined behaviour).
//@ fixed-by: D-138 — every PermCell access owes Creusot's `self == perm.ward()`, stated over the cell
//@ fixed-by: the call names.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; `unknown (timeout)` under D-138, on the
//@ teeth: identity owed at the `borrow_mut` under `q`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{cell::PermCell, ghost::perm::Perm, prelude::*};

pub struct S {
    pub c: PermCell<i32>,
    pub p: Ghost<Box<Perm<PermCell<i32>>>>,
    pub q: Ghost<Box<Perm<PermCell<i32>>>>,
}

#[ensures(result@ == 0)]
pub fn f(s: &mut S) -> i32 {
    let r1 = unsafe { s.c.borrow_mut(ghost!(&mut **s.q)) };
    let r2 = unsafe { s.c.borrow(ghost!(&**s.p)) };
    let before = *r2;
    *r1 = 7;
    if *r2 == before { 0 } else { 1 }
}
