//@ expect: verify
//@ mechanism: control: `Vec<u8>::clear` has no drop obligation
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[ensures((^v)@.len() == 0)]
pub fn clr(v: &mut Vec<u8>) { v.clear() }
