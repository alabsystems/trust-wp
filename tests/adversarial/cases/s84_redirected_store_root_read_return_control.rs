//@ expect: verify
//@ xfail: an OVER-REFUSAL the return gate introduces, named rather than hidden: `x` is untouched (the store `*t = 7` went to `y` after the redirect) and this true postcondition VERIFIED before the gate (ACCEPTED, exit 0). The gate cannot tell a store through a borrow whose own address escaped from a store into `x` — both sit in one alias class — so it refuses the read (with the gate in place: unknown, exit 2). Retire this xfail when the gate distinguishes the redirected borrow's target; the false twin (`result == 7`) is refuted in both configurations.
//@ mechanism: control — a value local read after a store through a borrow that no longer points at it.
//@ accept-means: n/a (control)
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
    *t = 7;
    x
}
