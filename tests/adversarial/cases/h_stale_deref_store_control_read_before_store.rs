//@ expect: verify
//@ mechanism: control for h_stale_deref_store_* — the value was read into a local BEFORE the store
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires((*bor)@ == 0)]
pub fn read_before_store(bor: &mut i32) {
    let v = *bor;
    *bor = 5;
    need_zero(v);
}
