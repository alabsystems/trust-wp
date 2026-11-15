//@ expect: verify
//@ mechanism: the true twin of container_write_then_owner_overwritten — after the direct
//@ mechanism: write the owner really does hold the later value, and that must stay provable.
//@ accept-means: n/a (control) — this contract is TRUE.
extern crate creusot_std;
use creusot_std::prelude::*;
pub struct H<'a> { pub p: &'a mut i32 }
pub fn k() { let mut x = 5i32; { let h = H { p: &mut x }; *h.p = 7i32; } x = 9i32; proof_assert!(x == 9i32); }
