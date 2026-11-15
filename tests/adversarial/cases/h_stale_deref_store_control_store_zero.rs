//@ expect: verify
//@ xfail: the stale-read gate fails closed (obligation false) instead of rebinding *bor to the stored value; completeness cost of the prophecy-store fix
//@ mechanism: control for h_stale_deref_store_* — TRUE: the stored value is the one the callee needs
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires((*bor)@ == 7)]
pub fn store_zero(bor: &mut i32) {
    *bor = 0;
    need_zero(*bor);
}
