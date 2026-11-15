//@ expect: reject
//@ mechanism: a local generic callee instantiated at a type with an unchecked panicking Drop::drop drops it in a body checked only for generic T
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: f verified; eat drops a non-empty Vec<D> and panics.
//@ teeth: exit 0 on base 853ad732 (probe r_drop_generic_fn).
//@ also-verified: eat
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
struct D;
impl Drop for D { fn drop(&mut self) { panic!("boom") } }
#[ensures(true)]
pub fn eat<T>(_v: Vec<T>) {}
#[requires(v@.len() > 0)]
#[ensures(true)]
pub fn f(v: Vec<D>) { eat(v) }
