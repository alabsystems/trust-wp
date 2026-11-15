//@ expect: verify
//@ mechanism: the true control of structpat_let_destructure_requires_reorder: the same
//@ mechanism: reordered `let S { a: aa, b: _bb } = s;` in the requires, and a body that returns
//@ mechanism: the field the binding NAMES. Under the correct reading the contract is true; under
//@ mechanism: the written-position reading `aa` denotes `b` and the control FAILS.
//@ accept-means: n/a (control).
//@ teeth: MEASURED on the merged tip 4e4613be (TRUST_WP_HARNESS_PROFILE=debug): failed, exit 1 —
//@ teeth: the reviewer's ld01c. A control that fails while its false twin verifies is the
//@ teeth: other half of the evidence that written order decided the verdict.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires({ let S { a: aa, b: _bb } = s; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b: _b, a } => a } }
