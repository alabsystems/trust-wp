//@ expect: reject
//@ mechanism: an uncontracted `&mut` helper framed a by-value parameter.
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
pub fn b07c(mut v: Vec<i32>) { let n = v.len(); push_one(&mut v); proof_assert!(n@ == v@.len()); }
