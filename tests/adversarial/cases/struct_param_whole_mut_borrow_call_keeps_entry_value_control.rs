//@ expect: verify
//@ mechanism: the TRUE twin of struct_param_whole_mut_borrow_call_keeps_entry_value.rs: the callee
//@ mechanism: states the value it writes and `caller` claims it.
//@ fixed-by: D-241: the value the parameter holds after the borrow is named apart from its entry value, so the entry fact and the callee's `(^t).a@ == 4` no longer land on one term; xfail retired.
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
pub fn reset(t: &mut P) {
    t.a = 4;
}

#[requires(s.a@ == 3)]
#[ensures(result@ == 4)]
pub fn caller(mut s: P) -> i32 {
    reset(&mut s);
    s.a
}
