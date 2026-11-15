//@ expect: reject
//@ mechanism: an enum-variant struct pattern written in NON-declaration field order.
//@ mechanism: `E::C { a: u32, b: A }` is matched as `E::C { b: bb, a: aa }`, so `aa` binds
//@ mechanism: the u32 field. If the driver types pattern fields POSITIONALLY in source
//@ mechanism: order against DECLARATION order, `aa` is typed as `A` and `A::view()` answers
//@ mechanism: 5, "proving" a postcondition about a u32.
//@ accept-means: a logic function of the WRONG type answers for a binding, so any
//@ accept-means: postcondition written over a reordered struct pattern is discharged against
//@ accept-means: a different field's type.
extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
pub enum E { C { a: u32, b: A }, N }
#[ensures(match e { E::C { b: bb, a: aa } => aa.view() == 5, E::N => true })]
pub fn g(e: E) {}
