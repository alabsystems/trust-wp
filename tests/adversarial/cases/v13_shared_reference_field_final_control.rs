//@ expect: verify
//@ mechanism: control for D-127's refusal of `^` over a projected field that may be a mutable
//@ mechanism: reference: a field that is a SHARED reference has no final value of its own, so `^` of
//@ mechanism: it is only the driver's image of a reborrow of the field's place, read by Creusot's rule
//@ mechanism: `(^x).c`. Setting the cell a `&Cell` field names, read through a copy of the field, must
//@ mechanism: keep verifying a postcondition that says nothing of the cell. The contract oracle's
//@ mechanism: `InteriorWrite` shape covers the same bodies under other clauses.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

pub struct SC<'a> {
    pub c: &'a Cell<i32>,
}

#[requires(x < 100i32 && x > -100i32)]
#[ensures(0i32 == 0i32)]
pub fn sc_set(p: &mut SC<'_>, x: i32) {
    let c = p.c;
    c.set(x);
}

#[requires(x < 100i32 && x > -100i32)]
#[ensures(0i32 == 0i32)]
pub fn boxed_sc_set(p: &mut Box<SC<'_>>, x: i32) {
    let c = p.c;
    c.set(x);
}
