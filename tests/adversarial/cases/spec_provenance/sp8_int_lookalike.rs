//@ expect: reject
//@ mechanism: local `crate::trust_wp_std::logic::Int` prints like the spec-library Int; Int passthroughs chosen by path
//@ accept-means: a local lookalike Int received trust_wp_std Int arithmetic semantics
//@ verdict: error
//@ refused-with: local item `crate::trust_wp_std` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod trust_wp_std { pub mod logic {
    #[derive(Clone, Copy)]
    pub struct Int(pub i64);
    impl ::core::convert::From<u32> for Int { fn from(_x: u32) -> Int { Int(0) } }
} }
#[ensures(result.0 == 5i64)]
pub fn i() -> crate::trust_wp_std::logic::Int { crate::trust_wp_std::logic::Int::from(5u32) }
