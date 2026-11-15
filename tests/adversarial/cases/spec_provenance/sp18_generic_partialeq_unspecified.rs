//@ expect: reject
//@ mechanism: generic T: PartialEq with no contract; a == a was translated to logical equality although the impl is unknown
//@ accept-means: an unknown impl of PartialEq was assumed reflexive
//@ teeth: verified (exit 0) on merge-base 72db95ee and on wp-s38 dca3a0be (table gate alone; fixed by the eq-recogniser type restriction)
use creusot_std::prelude::*;
#[ensures(result)]
pub fn g<T: PartialEq>(a: T) -> bool { a == a }
