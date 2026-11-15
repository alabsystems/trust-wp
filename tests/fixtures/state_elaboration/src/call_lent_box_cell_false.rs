// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A shared reference to a referent that owns a cell through a `Box` lends
//! the borrow: `Box<Cell<T>>` is `Freeze` (the cell is not inline), yet the
//! holder of a `&Box<Cell<T>>` writes the cell. `Freeze` alone called such a
//! result borrow-free, so the callee's lane proved its pre-Creusot
//! `*p == old(*p)` as `^p == *p` and each call read it the same way: every
//! contract below is false.

#![allow(unused)]

use std::cell::Cell;

use trust_wp::prelude::*;

pub struct H {
    pub c: Box<Cell<i32>>,
}

impl H {
    #[ensures(*self == old(*self))]
    pub fn peek(&mut self) -> &Box<Cell<i32>> {
        &self.c
    }
}

// FALSE: the cell is left 5.
#[ensures(^h == *h)]
pub fn peek_caller(h: &mut H) {
    let c = h.peek();
    c.set(5);
}

#[ensures(*p == old(*p))]
pub fn field(p: &mut H) -> &Box<Cell<i32>> {
    &p.c
}

// FALSE: the cell is left 5.
#[ensures(^h == *h)]
pub fn field_caller(h: &mut H) {
    let c = field(h);
    c.set(5);
}

#[ensures(*p == old(*p))]
pub fn give_box(p: &mut Box<Cell<i32>>) -> &Box<Cell<i32>> {
    &*p
}

// FALSE: the cell is left 5.
#[ensures(^x == *x)]
pub fn give_box_caller(x: &mut Box<Cell<i32>>) {
    let c = give_box(x);
    c.set(5);
}

fn main() {}
