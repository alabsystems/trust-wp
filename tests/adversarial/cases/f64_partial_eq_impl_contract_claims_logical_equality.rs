//@ expect: reject
//@ mechanism: a hand-written `PartialEq` impl over an `f64` field whose contract states logical equality
//@ mechanism: of the fields, while its body compares them with IEEE-754 `==`. Read over the reals, the
//@ mechanism: body meets the contract. The impl-method spelling of f64_eq_contract_restates_operator.rs.
//@ accept-means: `W(f64::NAN).eq(&W(f64::NAN))` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`<W as std::cmp::PartialEq>::eq verified`) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W(pub f64);

impl PartialEq for W {
    #[ensures(result == (self.0 == other.0))]
    fn eq(&self, other: &W) -> bool {
        self.0 == other.0
    }
}
