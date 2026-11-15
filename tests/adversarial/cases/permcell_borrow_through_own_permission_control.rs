//@ expect: verify
//@ mechanism: the TRUE twin of permcell_borrow_through_other_permission_uncharged.rs: both borrows
//@ mechanism: go through `p`, which the caller requires to guard the cell, so the borrow checker keeps
//@ mechanism: them apart and the read after the write sees it.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ xfail: `f unknown (timeout)` when committed: the read after the write through `r1` is not
//@ xfail: proved within the budget, with no permission obligation owed at either call.
//@ teeth: control — `unknown (timeout)` when committed.
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

#[requires(*s.p.ward() == s.c)]
#[ensures(result@ == 1)]
pub fn f(s: &mut S) -> i32 {
    let r1 = unsafe { s.c.borrow_mut(ghost!(&mut **s.p)) };
    *r1 = 7;
    let r2 = unsafe { s.c.borrow(ghost!(&**s.p)) };
    if *r2 == 7 { 1 } else { 0 }
}
