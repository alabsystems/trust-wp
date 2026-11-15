//@ expect: reject
//@ mechanism: local Box lookalike outside the reserved roots; Box::new recognised by printed-path suffix
//@ teeth: NONE on the pre-fix driver (already FAILED there, per review); kept as a regression guard only. sp12-sp20 are the cases that fail only with DefId/instance gating
//@ accept-means: a local `Box::new` that drops its argument was given Box identity semantics
use creusot_std::prelude::*;
pub mod boxed {
    pub struct Box<T>(pub Option<T>);
    impl<T> Box<T> { pub fn new(_x: T) -> Self { Box(None) } }
}
#[ensures(result)]
pub fn b() -> bool { let x = crate::boxed::Box::new(3u32); match x.0 { Some(v) => v == 3, None => false } }
