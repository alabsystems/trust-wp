//@ expect: reject
//@ mechanism: a `proof_assert!`'s field access is placed with the containing function's
//@ mechanism: name->index table, built from its SIGNATURE's types
//@ mechanism: (`proof_assert_extract::simplification`). `b.y` is `B`'s field 0; the signature holds
//@ mechanism: `A`, whose `y` is field 1, so the assertion reads field 1 of `B { y: 0, x: 5 }`.
//@ accept-means: an assertion about a local of a type the signature does not name is checked
//@ accept-means: against another field of that local.
//@
//@ WHY THE ASSERTION IS FALSE, as a concrete execution: at the assertion b.y is 0, not 5.
//@ teeth: MEASURED as ACCEPTED, exit 0 (`proof_assert in ...::wrong_assert verified`), on the
//@ teeth: campaign's driver and on main's when committed. RED: no fix in this tree.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A {
    pub x: i32,
    pub y: i32,
}

pub struct B {
    pub y: i32,
    pub x: i32,
}

pub fn wrong_assert(a: A) {
    let _ = a;
    let b = B { y: 0, x: 5 };
    proof_assert!(b.y == 5i32);
}
