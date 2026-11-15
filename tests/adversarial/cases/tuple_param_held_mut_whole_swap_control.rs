//@ expect: verify
//@ xfail: D-181 refuses a postcondition that reads a held `&mut` whole, true ones included: the
//@ xfail: lanes read such a read as a current value in the owner and as the borrow at each call.
//@ mechanism: control for the `tuple_param_held_mut_whole_*` cases: the body swaps, so the clause is
//@ mechanism: true, and the caller's two assertions follow from it in Creusot's reading. It is the
//@ mechanism: projected_deref_write_verify e2e fixture in Creusot's dialect.
//@ teeth: n/a (control). It verified on the build that counts a held `&mut` read whole as placed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == (x.1, x.0))]
pub fn f<'a>(x: (&'a mut u32, &'a mut u32)) -> (&'a mut u32, &'a mut u32) {
    (x.1, x.0)
}

pub fn caller() {
    let mut a = 0u32;
    let mut b = 0u32;
    let p = f((&mut a, &mut b));
    *p.0 = 10u32;
    proof_assert!(b == 10u32);
    proof_assert!(a == 0u32);
}
