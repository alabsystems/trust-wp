//@ expect: reject
//@ mechanism: crate-root `Seq` prints as bare `Seq`, like the spec library's re-exported Seq; not covered by the reserved-root backstop
//@ accept-means: a local lookalike Seq received the spec library's Seq::len semantics (real 7)
use creusot_std::prelude::*;
pub struct Seq<T>(pub Option<T>);
impl<T> Seq<T> {
    pub fn empty() -> Self { Seq(None) }
    pub fn len(&self) -> usize { 7 }
}
#[ensures(result@ == 0)]
pub fn f() -> usize { let s: Seq<u32> = Seq::empty(); s.len() }
