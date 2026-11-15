//@ expect: reject
//@ mechanism: `push_one(&mut self.v)` on a by-value self: the owner havoc was tied back to the entry symbol.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: a field borrow of a by-value owner frames the field again.
//@ WHY THE PROGRAM IS WRONG: push_one pushes, so the length grows by one.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S { v: Vec<i32> }
fn push_one(v: &mut Vec<i32>) { v.push(1); }
impl S { pub fn f(mut self) { let n = self.v.len(); push_one(&mut self.v); proof_assert!(n@ == self.v@.len()); } }
