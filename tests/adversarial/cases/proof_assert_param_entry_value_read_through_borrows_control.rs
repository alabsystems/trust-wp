//@ expect: verify
//@ mechanism: control for proof_assert_param_entry_value_read_through_borrows.rs: a shared borrow
//@ mechanism: of a by-value parameter, whole or of a field, taken before or after a write, and handed
//@ mechanism: to a callee or a method, reads the value the parameter has when the borrow is taken,
//@ mechanism: while a copy taken before the write keeps the entry value and its `#[requires]`.
//@ accept-means: n/a (control) — every claim here holds in every execution.
//@ fixed-by: n/a (control)
//@ teeth: on D-240 `whole_ref_ok` and `branch_rebind_ok` are FAILED, `copy_then_read_call_ok`
//@ teeth: `unknown` (vacuous: `x == x + 1`) and `method_after_field_write_ok` `unknown`; all verified
//@ teeth: with D-241.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == *a)]
pub fn read(a: &u32) -> u32 {
    *a
}

pub struct P {
    pub a: u32,
    pub b: u32,
}

impl P {
    #[ensures(result == self.b)]
    pub fn second(&self) -> u32 {
        self.b
    }
}

#[requires(x@ == 0)]
pub fn shared_ref_after_rebind_ok(mut x: u32) {
    x = 5;
    let r = &x;
    proof_assert!((*r)@ == 5);
}

#[requires(p.0@ == 1)]
pub fn whole_ref_ok(mut p: (u32, u32)) {
    p.1 = 5;
    let r = &p;
    proof_assert!(r.0@ == 1 && r.1@ == 5);
}

#[requires(x@ < 10)]
pub fn copy_then_shared_borrow_ok(mut x: u32) {
    let y = x;
    x = 5;
    let r = &x;
    proof_assert!(y@ < 10 && (*r)@ == 5);
}

#[requires(x@ < 10)]
pub fn copy_then_read_call_ok(mut x: u32) {
    let y = x;
    x = x + 1;
    let r = read(&x);
    proof_assert!(r@ == y@ + 1);
}

#[requires(x@ < 10)]
pub fn borrow_before_write_ok(mut x: u32) {
    let r = &x;
    let v = *r;
    x = 7;
    proof_assert!(v@ < 10 && x@ == 7);
}

#[requires(p.a@ == 3)]
pub fn method_after_field_write_ok(mut p: P) {
    let k = p.a;
    p.b = 9;
    let s = p.second();
    proof_assert!(k@ == 3 && s@ == 9);
}

#[requires(x@ < 10)]
pub fn branch_rebind_ok(mut x: u32, c: bool) {
    if c {
        x = x + 1;
    }
    let y = x;
    proof_assert!(y@ < 11);
}
