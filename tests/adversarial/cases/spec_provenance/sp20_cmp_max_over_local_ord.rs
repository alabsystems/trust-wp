//@ expect: reject
//@ mechanism: core::cmp::max::<S> with a local Ord; std CMP_MAX contract describes a call whose T: Ord bound runs user code
//@ accept-means: a std generic fn received its contract while its trait bound ran user code
//@ teeth: pre-fix verdict not measured; rejected (FAILED) after the admission gate
use creusot_std::prelude::*;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd)]
pub struct S(pub u32);
impl Ord for S { fn cmp(&self, _o: &S) -> std::cmp::Ordering { std::cmp::Ordering::Equal } fn max(self, _o: S) -> S { S(1000) } }
#[ensures(result.0 == 1u32 || result.0 == 2u32)]
pub fn f() -> S { std::cmp::max(S(1), S(2)) }
