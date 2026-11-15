//@ expect: reject
//@ mechanism: the return-expression lane reads `*t` after `t` was redirected through a pointer to it (`let tt = &mut t; *tt = &mut y;`) as the pointee `t` was FIRST created on, so the returned `*t` is proved equal to `x` although `t` points at `y`.
//@ fixed-by: wp-s84 (the return gate counts a pointer-slot store for a read THROUGH a reference: a redirect changes where the deref goes)
//@ accept-means: a deref read after a redirect through `&mut &mut` is checked against the original target — a plain-Rust false accept in a `#[ensures]` clause.
//@ WHY THE PROGRAM IS WRONG: `*t` is `y`, which is 5, after `*tt = &mut y`; `result == 0` is false on every run.
//@ teeth: LIVE on the D1 build d309075a (and therefore on the tip, which this lane does not change): ACCEPTED,
//@ teeth: base_exit_code=0 on the false `result == 0` spelling;
//@ teeth: the true twin `result == 5` is REFUTED there. With the return gate: unknown, exit 2
//@ teeth: on the same program. PRE-EXISTING.
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[ensures(result == 0i32)]
pub fn k() -> i32 {
    let mut x = 0i32;
    let mut y = 5i32;
    let mut t: &mut i32 = &mut x;
    let tt: &mut &mut i32 = &mut t;
    *tt = &mut y;
    *t
}
