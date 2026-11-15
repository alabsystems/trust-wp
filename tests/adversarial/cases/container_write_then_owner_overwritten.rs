//@ expect: reject
//@ mechanism: a write through a container-held `&mut` records a value for the place the
//@ mechanism: borrow governs; a later DIRECT write to that same owner must retire the record,
//@ mechanism: or the older value keeps speaking for the owner forever.
//@ accept-means: any write-back the verifier records outlives the place it describes, so a
//@ accept-means: later assignment to that place is invisible and its old value stays provable.
//@ fixed-by: the direct-write lanes retire the deref sink, the name update and every borrower
//@ fixed-by: whose chain ends at the owner
//@ teeth: RED when the write-back generalization landed without the retirement: the FALSE
//@ teeth: assertion verified AND the true twin failed, wrong in both directions. Found by a
//@ teeth: reviewer outside the corpus, which is why it is owned here now.
extern crate creusot_std;
use creusot_std::prelude::*;
pub struct H<'a> { pub p: &'a mut i32 }
pub fn k() { let mut x = 5i32; { let h = H { p: &mut x }; *h.p = 7i32; } x = 9i32; proof_assert!(x == 7i32); }
