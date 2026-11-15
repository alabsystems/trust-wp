//@ expect: verify
//@ mechanism: the isolating twin of f64_partial_eq_impl_contract_claims_logical_equality.rs over an `i64`
//@ mechanism: field, where the program's `==` IS logical equality.
//@ accept-means: n/a (control) — the impl returns the logical equality of the fields.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W(pub i64);

impl PartialEq for W {
    #[ensures(result == (self.0 == other.0))]
    fn eq(&self, other: &W) -> bool {
        self.0 == other.0
    }
}
