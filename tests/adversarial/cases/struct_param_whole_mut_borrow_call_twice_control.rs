//@ expect: verify
//@ mechanism: control for struct_param_whole_mut_borrow_call_twice.rs: two calls in turn each state
//@ mechanism: what they leave, and the caller claims the second.
//@ accept-means: n/a (control)
//@ fixed-by: n/a (control)
//@ teeth: verified on D-240; vacuous with the one-level rename (`^^s` collapsed onto `^s`, which both
//@ teeth: postconditions pin), verified with D-241.
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

#[ensures((^t).a@ == 5)]
#[ensures((^t).b@ == (*t).b@)]
pub fn set5(t: &mut P) {
    let b = t.b;
    *t = P { a: 5, b };
}

#[ensures(result@ == 5)]
pub fn two_calls_ok(mut s: P) -> i32 {
    reset(&mut s);
    set5(&mut s);
    s.a
}
