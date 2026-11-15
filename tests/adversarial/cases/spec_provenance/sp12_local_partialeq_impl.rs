//@ expect: reject
//@ mechanism: local impl PartialEq whose eq returns false; a == a calls core::cmp::PartialEq::eq with Self=S (Std callee DefId), which reached the trait-level std PARTIAL_EQ contract and the logical-== eq recogniser
//@ accept-means: a local impl of a std trait received std's concrete trait-level contract
//@ teeth: verified (exit 0) on wp-s38 c9551d2b and on merge-base 72db95ee (review probe t1)
use creusot_std::prelude::*;
#[derive(Clone, Copy)]
pub struct S(pub u32);
impl PartialEq for S { fn eq(&self, _o: &S) -> bool { false } }
#[ensures(result)]
pub fn f() -> bool { let a = S(1); a == a }
