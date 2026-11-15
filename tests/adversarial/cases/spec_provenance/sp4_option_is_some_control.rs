//@ expect: verify
//@ mechanism: real Option::is_some keeps its core contract
//@ accept-means: n/a (control)
use creusot_std::prelude::*;
#[ensures(result == true)]
pub fn o() -> bool { let x = Some(1u32); x.is_some() }
