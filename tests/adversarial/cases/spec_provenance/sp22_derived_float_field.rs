//@ expect: reject
//@ mechanism: #[derive(PartialEq)] over an f64 field; derived eq is not reflexive (NaN), so it is not logical equality
//@ accept-means: float PartialEq was modelled as logical equality
//@ teeth: pre-fix verdict not measured; guards the float exclusion of partial_eq_is_logical_equality
use creusot_std::prelude::*;
#[derive(Clone, Copy, PartialEq)]
pub struct F(pub f64);
#[ensures(result)]
pub fn f(x: F) -> bool { x == x }
