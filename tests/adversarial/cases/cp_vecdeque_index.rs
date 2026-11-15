//@ expect: reject
//@ mechanism: generic Index fallback assumed the impl panic-free
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `v[3]` on a VecDeque of unknown length verified.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::collections::VecDeque;

#[requires(true)]
pub fn dq(v: &VecDeque<u8>) -> u8 {
    v[3]
}
