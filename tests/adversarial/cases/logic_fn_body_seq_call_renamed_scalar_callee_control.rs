//@ expect: verify
//@ mechanism: control for logic_fn_body_seq_call_renamed whose claim the encoder can prove: the function renamed onto `seq` returns an `Int`, so the call is read as that function (`twice`) only if the rename is followed; read as the sequence literal it has another sort and the claim is not proved.
//@ accept-means: n/a (control) — `caller(y)` is `twice(y)`, `y + y`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn twice(x: Int) -> Int {
    x + x
}

use crate::twice as seq;

#[logic]
#[ensures(result == y + y)]
pub fn caller(y: Int) -> Int {
    seq(y)
}
