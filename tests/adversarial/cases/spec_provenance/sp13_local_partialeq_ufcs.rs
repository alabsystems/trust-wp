//@ expect: reject
//@ mechanism: same as sp12 through UFCS <S as PartialEq>::eq
//@ accept-means: a local impl of a std trait received std's concrete trait-level contract via UFCS
//@ teeth: verified (exit 0) on wp-s38 c9551d2b (review probe t2)
use creusot_std::prelude::*;
#[derive(Clone, Copy)]
pub struct S(pub u32);
impl PartialEq for S { fn eq(&self, _o: &S) -> bool { false } }
#[ensures(result)]
pub fn f() -> bool { let a = S(1); <S as PartialEq>::eq(&a, &a) }
