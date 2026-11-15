//@ expect: verify
//@ mechanism: control: checked_div(MIN, -1).is_none().
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ teeth: control - must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)] pub fn f() { let x = i64::MIN; let m = -1i64; let r = x.checked_div(m); proof_assert!(r.is_none()); }
