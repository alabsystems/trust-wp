//@ expect: verify
//@ mechanism: control for the value symbol of an untranslated cast (D-169): `a as usize` twice, `a` a
//@ mechanism: parameter never reassigned nor written behind the walk's back, is one value, so the two
//@ mechanism: bindings are one symbol and `x == y` holds. The body carries a clause, so no cap applies.
//@ mechanism: Twin of untranslated_cast_of_reassigned_parameter_panic_arm.rs, whose casts read two values.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
#[ensures(result)]
pub fn f(a: *const u8) -> bool {
    let x = a as usize;
    let y = a as usize;
    x == y
}
