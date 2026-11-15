//@ expect: reject
//@ mechanism: an uncontracted `set7(&mut t.0)` on a local tuple field framed the field.
//@ fixed-by: wp-s48 (a call advances every &mut argument; field-borrow owners advance to Final(owner))
//@ accept-means: an opaque callee advances no &mut field-borrow argument again.
//@ WHY THE PROGRAM IS WRONG: set7 writes 7, so t.0 is no longer 3.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87 (probe f3), measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn set7(x: &mut u32) {
    *x = 7;
}

pub fn f3() {
    let mut t = (3u32, 4u32);
    set7(&mut t.0);
    proof_assert!(t.0@ == 3);
}
