//@ expect: reject
//@ mechanism: `push_one(&mut s.v)` on a by-value struct parameter framed the field.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: a field borrow of a by-value parameter frames the field again.
//@ WHY THE PROGRAM IS WRONG: push_one pushes, so the length grows by one.
//@ teeth: verified (exit 0) on wp-s48 c4516c44 (positions fix only), measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S { pub v: Vec<i32> }
fn push_one(v: &mut Vec<i32>) { v.push(1); }
pub fn f1(mut s: S) { let n = s.v.len(); push_one(&mut s.v); proof_assert!(n@ == s.v@.len()); }
