//@ expect: reject
//@ mechanism: `mut_borrow::may_carry_borrow` decides a `&T` result lends nothing when `T` is
//@ mechanism: `Freeze` and carries no borrow. `Box<Cell<i32>>` is `Freeze` (the cell is behind the
//@ mechanism: box, not inline), yet the holder of a `&Box<Cell<i32>>` writes the cell. So D-102's
//@ mechanism: single lending decision reads `peek`'s pre-Creusot `*self` as `^self` in its own lane
//@ mechanism: (proved: the body frees no prophecy) and at the call (the region rule it replaced
//@ mechanism: refused it there).
//@ accept-means: `peek_caller` is credited with `^h == *h` from a callee whose result it writes
//@ accept-means: the cell through.
//@ WHY THE CONTRACT IS FALSE: `c.set(5)` writes the cell `h` owns through the returned reference,
//@ WHY THE CONTRACT IS FALSE: so `^h` holds 5 while the entry `*h` holds anything.
//@ fixed-by: D-107 (`mut_borrow::may_carry_borrow` counts a `&T` from which
//@ fixed-by: `extract::ty_exposes_interior_mutability` reaches a cell)
//@ teeth: MEASURED (debug driver): cbadb52d `H::peek verified`, `peek_caller unknown`;
//@ teeth: 57a163d8 and 576532d7 `H::peek verified` AND `peek_caller verified`. On the D-107
//@ teeth: tree `peek`'s clause is refused (the result may borrow `self`) and `peek_caller` is
//@ teeth: unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

pub struct H {
    pub c: Box<Cell<i32>>,
}

impl H {
    #[ensures(*self == old(*self))]
    pub fn peek(&mut self) -> &Box<Cell<i32>> {
        &self.c
    }
}

#[ensures(^h == *h)]
pub fn peek_caller(h: &mut H) {
    let c = h.peek();
    c.set(5);
}
