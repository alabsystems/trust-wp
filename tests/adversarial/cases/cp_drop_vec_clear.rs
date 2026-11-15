//@ expect: reject
//@ mechanism: `Vec::<D>::clear` drops elements inside std: the call owes D's drop obligation (unchecked panicking Drop::drop)
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: clr verified; it panics for any non-empty vector.
//@ teeth: exit 0 on HEAD 5780c31e and base 853ad732 (review probe r_drop_vec_clear).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
struct D;
impl Drop for D { fn drop(&mut self) { panic!("boom") } }
#[requires(v@.len() > 0)]
#[ensures(true)]
pub fn clr(v: &mut Vec<D>) { v.clear() }
