//@ expect: reject
//@ mechanism: local `crate::std::process::abort` returns normally; recognising it as diverging proves the fallthrough unreachable
//@ accept-means: a normally-returning local fn was treated as std abort
//@ verdict: error
//@ refused-with: local item `crate::std` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod std { pub mod process { pub fn abort() {} } }
#[ensures(false)]
pub fn a() { crate::std::process::abort() }
