//@ expect: reject
//@ mechanism: `Option::insert` drops the previous value inside std
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: f verified; it panics when o is Some.
//@ teeth: exit 0 on base 853ad732 (probe r_drop_option_insert).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct D;
impl Drop for D { fn drop(&mut self) { panic!("boom") } }
#[ensures(true)]
pub fn f(o: &mut Option<D>) { o.insert(D); }
