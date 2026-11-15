//@ expect: reject
//@ mechanism: storing through an alias of a `&mut` slot REDIRECTS it. Facts recorded for what
//@ mechanism: the slot used to point at must retire with the redirect, or a later read through
//@ mechanism: the slot resolves to the old owner and reads a value that write never put there.
//@ accept-means: a redirected borrow keeps answering for its former target, so any write before
//@ accept-means: the redirect can be read back through it afterwards.
//@ fixed-by: ?
//@ teeth: FALSE by execution — the stripped program prints v = 9. Found by a reviewer outside
//@ teeth: the corpus when flow-sensitive resolution first modelled the redirect: the write lane
//@ teeth: learned the slot had moved while the read lane kept answering from the old edge.
//@ note: the TRUE twin of this program does not verify either, at this tip or before the
//@ note: flow-sensitive work — retiring the stale facts is sound but does not rebuild the new
//@ note: target, so `v == 9` stays unprovable. That is a pre-existing incompleteness, measured
//@ note: on both sides, not a price paid here.
extern crate creusot_std;
use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut y = 9i32;
    let mut r: &mut i32 = &mut x;
    *r = 1i32;
    { let rr: &mut &mut i32 = &mut r; *rr = &mut y; }
    let v = *r;
    proof_assert!(v == 1i32);
}
