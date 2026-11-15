//@ expect: reject
//@ mechanism: checked_add overflow returns None, so unwrap panics.
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the unwrap requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: unwrap on None panics.
//@ teeth: rejected only as unknown (quantifier-unhandled) on b98d5d87; verified on the s43 v2 review build.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ == i64::MAX@)] #[ensures(true)] pub fn f(x: i64) -> i64 { x.checked_add(1).unwrap() }
