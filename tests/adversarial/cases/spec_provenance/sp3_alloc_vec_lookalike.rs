//@ expect: reject
//@ mechanism: local `crate::alloc::vec::Vec` prints `alloc::vec::Vec`; Vec::new/push/len specs chosen by printed path
//@ accept-means: a local lookalike Vec received alloc Vec's contracts (real len 7)
//@ verdict: error
//@ refused-with: local item `crate::alloc` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod alloc { pub mod vec {
    pub struct Vec<T>(pub Option<T>);
    impl<T> Vec<T> {
        pub fn new() -> Self { Vec(None) }
        pub fn len(&self) -> usize { 7 }
        pub fn push(&mut self, _x: T) {}
    }
} }
#[ensures(result@ == 1)]
pub fn v() -> usize { let mut x = crate::alloc::vec::Vec::new(); x.push(1u32); x.len() }
