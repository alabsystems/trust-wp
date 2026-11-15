//@ expect: reject
//@ also-verified: mk
//@ mechanism: a callee's `ensures` and the caller's body read of the same field must be placed by
//@ mechanism: one table. `mk`'s `result.x`/`result.y` are `B`'s fields 1 and 0; the caller's body
//@ mechanism: read `b.y` is placed with the caller's signature table (`A`, where `y` is field 1).
//@ mechanism: Read with the caller's table too, the credit and the read are wrong the same way and
//@ mechanism: the claim is refuted; read with the callee's table alone, the credit says field 1 is
//@ mechanism: 5 and the body returns field 1, so the false claim verifies.
//@ accept-means: a call's credit and a body read of the value it describes name different fields.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: wrong(A { x: 0, y: 0 }) returns mk().y,
//@ which is 0, not 5.
//@ teeth: MEASURED as ACCEPTED, exit 0 (`wrong verified`), on the driver that reads a callee's
//@ teeth: clauses with the callee's own field table and leaves body reads on the caller's; rejected
//@ teeth: (`wrong FAILED`) at the campaign tip. A guard on the named-field placement class
//@ teeth: (named_field_callee_requires_read_with_caller_field_table.rs): a fix that moves one lane
//@ teeth: to the right table while another stays on the wrong one opens this.
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

#[ensures(result.x == 5i32 && result.y == 0i32)]
pub fn mk() -> B {
    B { y: 0, x: 5 }
}

#[ensures(result == 5i32)]
pub fn wrong(a: A) -> i32 {
    let _ = a;
    let b = mk();
    b.y
}
