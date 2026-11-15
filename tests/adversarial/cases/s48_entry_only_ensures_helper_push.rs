//@ expect: reject
//@ mechanism: a callee whose ensures mention only the entry `*v` framed `^v`.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: a contract that does not mention `^v` frames the argument again.
//@ WHY THE PROGRAM IS WRONG: len_then_push pushes, so n is the old length.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == (*v)@.len())]
fn len_then_push(v: &mut Vec<i32>) -> usize { let l = v.len(); v.push(1); l }
pub fn k(mut v: Vec<i32>) { let n = len_then_push(&mut v); proof_assert!(n@ == v@.len()); }
