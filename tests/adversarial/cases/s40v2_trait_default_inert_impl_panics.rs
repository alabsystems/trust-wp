//@ expect: reject
//@ mechanism: inertness was judged on the trait DEFAULT body of an unresolved T::die(), not the impl that runs
//@ accept-means: S::die panics and f::<S>(0) reaches it. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: verified on 8147c10d (s40 review probe p04)
//@ also-verified: Tr::die
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr { fn die() -> ! { loop {} } }
pub struct S;
impl Tr for S { fn die() -> ! { panic!() } }
#[ensures(true)]
pub fn f<T: Tr>(x: i32) { if x <= 0 { T::die() } }
