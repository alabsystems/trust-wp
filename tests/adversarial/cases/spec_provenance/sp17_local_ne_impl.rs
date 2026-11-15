//@ expect: reject
//@ mechanism: local ne returning true; a != a received std NE / logical !=
//@ accept-means: a local ne impl received std's NE contract
//@ teeth: verified (exit 0) on wp-s38 c9551d2b and on merge-base 72db95ee (review probe t14)
use creusot_std::prelude::*;
#[derive(Clone, Copy)]
pub struct S(pub u32);
impl PartialEq for S { fn eq(&self, _o: &S) -> bool { true } fn ne(&self, _o: &S) -> bool { true } }
#[ensures(!result)]
pub fn f() -> bool { let a = S(1); a != a }
