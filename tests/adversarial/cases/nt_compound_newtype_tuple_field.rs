//@ expect: reject
//@ mechanism: compound single-field struct whose field is a tuple must keep its projection (df47962)
//@ accept-means: t.0 was collapsed onto t so the two tuple components became indistinguishable
//@ teeth: regression guard; rejected at df47962 and after (review probe nt2::d_tup)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Tp(pub (u64, u64));

#[ensures(result == t.0.1)]
pub fn wrong_component(t: &Tp) -> u64 {
    t.0.0
}
