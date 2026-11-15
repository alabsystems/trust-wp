//@ expect: reject
//@ mechanism: #[derive(PartialEq)] Outer whose field Inner has a hand-written eq returning false; derived eq is logical equality only when every field eq is
//@ accept-means: the derived-impl logical-equality rule ignored a non-logical field impl
//@ teeth: pre-fix verdict not measured; guards the recursive field condition of partial_eq_is_logical_equality
use creusot_std::prelude::*;
#[derive(Clone, Copy)]
pub struct Inner(pub u32);
impl PartialEq for Inner { fn eq(&self, _o: &Inner) -> bool { false } }
#[derive(Clone, Copy, PartialEq)]
pub struct Outer { pub a: Inner, pub b: u32 }
#[ensures(result)]
pub fn f(x: Outer) -> bool { x == x }
