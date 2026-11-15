//@ expect: verify
//@ mechanism: control: a struct holding `&u8` (Freeze pointee) is not a write capability
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct S<'a> { pub r: &'a u8 }
#[ensures(true)]
pub fn look(s: S) -> u8 { *s.r }
#[ensures(result == true)]
pub fn same(x: &u8) -> bool {
    let a = *x;
    look(S { r: x });
    let b = *x;
    a == b
}
