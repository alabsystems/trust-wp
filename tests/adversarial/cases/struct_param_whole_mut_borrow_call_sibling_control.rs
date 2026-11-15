//@ expect: verify
//@ mechanism: control for struct_param_whole_mut_borrow_call_keeps_entry_value.rs: the callee says it
//@ mechanism: leaves `b` alone, so the entry fact about `s.b` reaches the value after the call through
//@ mechanism: the callee's postcondition, not by reading the entry value as the current one.
//@ mechanism: `reset` writes the whole pointee (`*t = P { a: 4, b }`): the field store `t.a = 4`
//@ mechanism: makes the callee's own frame proof slow enough to time out under load.
//@ accept-means: n/a (control)
//@ fixed-by: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: i32,
    pub b: i32,
}

#[ensures((^t).a@ == 4)]
#[ensures((^t).b@ == (*t).b@)]
pub fn reset(t: &mut P) {
    let b = t.b;
    *t = P { a: 4, b };
}

#[requires(s.b@ == 3)]
#[ensures(result@ == 3)]
pub fn keeps_b(mut s: P) -> i32 {
    reset(&mut s);
    s.b
}
