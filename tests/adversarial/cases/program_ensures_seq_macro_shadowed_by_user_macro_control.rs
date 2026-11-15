//@ expect: verify
//@ mechanism: control for program_ensures_seq_macro_shadowed_by_user_macro, differing in the crate's `macro_rules! seq` alone: `seq![5]` is the prelude's one-element literal.
//@ accept-means: n/a (control) — the length of `seq![5]` is `1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(seq![5].len() == 1)]
pub fn prog() {}
