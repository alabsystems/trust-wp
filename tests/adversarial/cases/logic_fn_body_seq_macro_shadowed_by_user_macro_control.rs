//@ expect: verify
//@ mechanism: control for logic_fn_body_seq_macro_shadowed_by_user_macro, differing in the crate's `macro_rules! seq` alone: `seq![5]` is the prelude's one-element literal.
//@ accept-means: n/a (control) — the length of `seq![5]` is `1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == 1)]
pub fn caller() -> Int {
    seq![5].len()
}
