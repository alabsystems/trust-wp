//@ expect: reject
//@ mechanism: local View plus a local eq returning false; a == a received PARTIAL_EQ over the user view
//@ accept-means: a local eq impl was modelled as equality of the user View
//@ teeth: verified (exit 0) on wp-s38 c9551d2b (review probe t5)
use creusot_std::prelude::*;
pub struct W(pub u32);
impl View for W { type ViewTy = Int; #[logic(open)] fn view(self) -> Int { pearlite! { self.0@ } } }
impl PartialEq for W { fn eq(&self, _o: &W) -> bool { false } }
#[ensures(result)]
pub fn f(a: &W) -> bool { a == a }
