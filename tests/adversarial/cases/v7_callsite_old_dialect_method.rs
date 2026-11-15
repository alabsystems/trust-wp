//@ expect: reject
//@ mechanism: the same call-site misreading through a `&mut self` method: the callee's
//@ mechanism: `self.v == x` (the value `self` is left with, since the clause reads `old(self.v)`)
//@ mechanism: is read at the call as the receiver's value before the call.
//@ accept-means: the field value `put` hands back is the one it stores.
//@ WHY THE CONTRACT IS FALSE: with c.v = 1 at entry, `c.put(3)` returns 1.
//@ fixed-by: D-101 (and a field of a `&mut` parameter is a field of its referent, read at the state `*p` is)
//@ teeth: MEASURED on d73d0571 (debug driver): `put_caller verified`. On the D-101 tree: unknown.
//@ also-verified: Cell::put
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct Cell {
    pub v: i32,
}

impl Cell {
    #[ensures(self.v == x && result == old(self.v))]
    pub fn put(&mut self, x: i32) -> i32 {
        let o = self.v;
        self.v = x;
        o
    }
}

#[ensures(result == 3i32)]
pub fn put_caller(c: &mut Cell) -> i32 {
    c.put(3)
}
