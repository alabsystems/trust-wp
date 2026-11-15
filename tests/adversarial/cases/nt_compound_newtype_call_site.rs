//@ expect: reject
//@ mechanism: compound single-field struct newtype: callee contract and call-site facts must agree on w.0 (02_fib panic shape, df47962)
//@ accept-means: the call-site assumption of e_callee was instantiated on a term other than the caller's w.0
//@ teeth: regression guard; rejected at df47962 and after (review probe nt3::e_caller)
//@ also-verified: callee
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[ensures(result@ == w.0@.len())]
pub fn callee(w: &W) -> usize {
    w.0.len()
}

#[requires(w.0@.len() == 3)]
#[ensures(result@ == 4)]
pub fn caller(w: &W) -> usize {
    callee(w)
}
