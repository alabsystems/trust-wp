//@ expect: verify
//@ mechanism: control for h_stale_deref_store_* — the read precedes the store, so it is not stale (the gate is flow-sensitive)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires((*bor)@ == 0)]
pub fn call_before_store(bor: &mut i32) {
    need_zero(*bor);
    *bor = 5;
}
