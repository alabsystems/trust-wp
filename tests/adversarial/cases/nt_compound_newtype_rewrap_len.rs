//@ expect: reject
//@ mechanism: compound single-field struct newtype collapse: result built by rewrapping the parameter's field
//@ accept-means: the rewrap W(w.0) was encoded with a length unrelated to w.0
//@ teeth: regression guard; rejected at df47962 and after (review probe nt1::a_rewrap)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[ensures(result.0@.len() == w.0@.len() + 1)]
pub fn rewrap_grows(w: W) -> W {
    W(w.0)
}
