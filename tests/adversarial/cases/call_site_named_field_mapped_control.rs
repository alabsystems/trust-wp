//@ expect: verify
//@ mechanism: call_site_named_field_unmapped_control with the callee's parameter type also
//@ mechanism: in the CALLER's signature, which is the only difference. The caller's flat
//@ mechanism: field table then knows the name, the imported clause is rewritten to the
//@ mechanism: positional accessor, and the very same struct literal discharges the very
//@ mechanism: same obligation. The pair is what pins the cause on the table's scope rather
//@ mechanism: than on struct literals being undecidable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[requires(s.a@ == 4)]
#[ensures(result@ == 4)]
pub fn f(s: S) -> i32 {
    s.a
}

#[ensures(result@ == 4)]
pub fn caller(_z: S) -> i32 {
    f(S { a: 4, b: 6 })
}
