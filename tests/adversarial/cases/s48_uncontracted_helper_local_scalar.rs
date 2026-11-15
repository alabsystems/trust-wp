//@ expect: reject
//@ mechanism: an uncontracted `set7(&mut a)` framed a local scalar.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: an opaque callee advances no &mut argument again.
//@ WHY THE PROGRAM IS WRONG: set7 writes 7.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn set7(x: &mut u32) { *x = 7; }
pub fn h() { let mut a = 3u32; set7(&mut a); proof_assert!(a@ == 3); }
