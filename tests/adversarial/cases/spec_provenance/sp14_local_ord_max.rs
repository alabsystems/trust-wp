//@ expect: reject
//@ mechanism: local Ord::max override returning S(1000); S(1).max(S(2)) received std Ord::max (result == self || result == other)
//@ accept-means: a local Ord impl received std's MAX contract
//@ teeth: verified (exit 0) on wp-s38 c9551d2b and on merge-base 72db95ee (review probe t3)
use creusot_std::prelude::*;
use core::cmp::Ordering;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd)]
pub struct S(pub u32);
impl Ord for S {
    fn cmp(&self, _o: &S) -> Ordering { Ordering::Less }
    fn max(self, _o: S) -> S { S(1000) }
}
#[ensures(result.0 == 1u32 || result.0 == 2u32)]
pub fn f() -> S { S(1).max(S(2)) }
