//@ expect: verify
//@ mechanism: real std Vec through the std re-export keeps its alloc Vec contracts
//@ accept-means: n/a (control)
use creusot_std::prelude::*;
#[ensures(result@ == 1)]
pub fn v() -> usize { let mut x = std::vec::Vec::new(); x.push(1u32); x.len() }
