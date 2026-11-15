//@ expect: reject
//@ mechanism: local PartialOrd::lt always true; a < a received std LT (result == (self@ < rhs@))
//@ accept-means: a local PartialOrd impl received std's LT contract
//@ teeth: verified (exit 0) on wp-s38 c9551d2b (review probe t4)
use creusot_std::prelude::*;
#[derive(Clone, Copy, PartialEq)]
pub struct S(pub u32);
impl PartialOrd for S {
    fn partial_cmp(&self, _o: &S) -> Option<core::cmp::Ordering> { None }
    fn lt(&self, _o: &S) -> bool { true }
}
#[ensures(!result)]
pub fn f() -> bool { let a = S(1); a < a }
