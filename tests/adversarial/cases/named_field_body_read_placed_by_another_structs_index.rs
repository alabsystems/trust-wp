//@ expect: reject
//@ mechanism: a body read of a named struct field is translated as `__trust_wp_field_<name>`
//@ mechanism: (`translate::place::typed_field_projection`) although the MIR names the field by its
//@ mechanism: index, and the function's contract rewrite then places the name with the table of
//@ mechanism: the function's SIGNATURE. `b.y` is `B`'s field 0; the signature holds `A`, whose `y`
//@ mechanism: is field 1, so the read becomes field 1 of the literal `B { y: 0, x: 5 }`, which is 5.
//@ accept-means: a local of a type the signature does not name reads another struct's field
//@ accept-means: position for any field name the two share.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: wrong(A { x: 0, y: 0 }) returns b.y, which
//@ is 0, not 5.
//@ teeth: MEASURED as ACCEPTED, exit 0 (`wrong verified`), on the campaign's driver and on main's
//@ teeth: when committed. RED: no fix in this tree.
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

#[ensures(result == 5i32)]
pub fn wrong(a: A) -> i32 {
    let _ = a;
    let b = B { y: 0, x: 5 };
    b.y
}
