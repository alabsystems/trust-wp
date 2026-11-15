//@ expect: reject
//@ mechanism: Option<S> == Option<S> runs core's Option eq which delegates to the local S::eq returning false; the std impl's T: PartialEq bound is discharged by user code
//@ accept-means: a std generic impl was described by its contract while its trait bound ran user code
//@ teeth: verified (exit 0) on merge-base 72db95ee and on wp-s38 dca3a0be (table gate alone; fixed by the eq-recogniser type restriction)
use creusot_std::prelude::*;
#[derive(Clone, Copy)]
pub struct S(pub u32);
impl PartialEq for S { fn eq(&self, _o: &S) -> bool { false } }
#[ensures(result)]
pub fn f() -> bool { let a = Some(S(1)); a == a }
