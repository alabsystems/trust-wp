//@ expect: reject
//@ mechanism: `set7(&mut p.a)` on a by-value parameter: the copy `n = p.a` was advanced and the owner framed.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: a field borrow of a by-value parameter frames the field again.
//@ WHY THE PROGRAM IS WRONG: set7 writes 7; the entry field is arbitrary.
//@ teeth: verified (exit 0) on wp-s48 c4516c44, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P { pub a: u32 }
fn set7(x: &mut u32) { *x = 7; }
pub fn f4(mut p: P) { let n = p.a; set7(&mut p.a); proof_assert!(n@ == p.a@); }
