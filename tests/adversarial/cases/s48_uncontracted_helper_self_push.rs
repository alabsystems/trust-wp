//@ expect: reject
//@ mechanism: an uncontracted `&mut` helper framed its argument: `push_one(&mut self)` left self unchanged.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: a callee with no contract frames its &mut argument again.
//@ WHY THE PROGRAM IS WRONG: push_one pushes, so the length grows by one.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn push_one(v: &mut Vec<i32>) { v.push(1); }
pub trait Tr { fn f(self); }
impl Tr for Vec<i32> { fn f(mut self) { let n = self.len(); push_one(&mut self); proof_assert!(n@ == self@.len()); } }
