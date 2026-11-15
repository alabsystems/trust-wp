//@ expect: reject
//@ also-verified: need
//@ mechanism: a callee's `requires` is parsed at the call with its field accesses still spelled
//@ mechanism: `__trust_wp_field_<name>`, and the caller's contract rewrite places them with the
//@ mechanism: CALLER's name->index table (`struct_field_map::build_struct_field_map` over the
//@ mechanism: caller). `b.x` is `B`'s field 1, but the caller's signature holds `A`, whose `x` is
//@ mechanism: field 0, so the call owes `B`'s field 0 (`y`, which is 5) and discharges it, while
//@ mechanism: the callee's own lane was granted `b.x == 5` over field 1.
//@ accept-means: a call owes a different field than the one the callee's body was granted, so a
//@ accept-means: violated precondition is discharged by an unrelated field of the argument.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: caller(A { x: 0, y: 0 }) calls
//@ need(B { y: 5, x: 0 }), whose `requires(b.x == 5)` is violated (b.x is 0).
//@ teeth: MEASURED as ACCEPTED, exit 0 (`caller verified`), on the campaign's driver and on
//@ teeth: main's when committed. RED: no fix in this tree. Reading the callee's clause with the
//@ teeth: callee's table closes it and opens named_field_callee_ensures_placed_apart_from_body_read
//@ teeth: through the body-read spelling, so the class needs every lane placed by the receiver's
//@ teeth: type, not one lane moved.
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

#[requires(b.x == 5i32)]
#[ensures(result == 5i32)]
pub fn need(b: B) -> i32 {
    b.x
}

#[ensures(result == 5i32)]
pub fn caller(a: A) -> i32 {
    let _ = a;
    need(B { y: 5, x: 0 })
}
