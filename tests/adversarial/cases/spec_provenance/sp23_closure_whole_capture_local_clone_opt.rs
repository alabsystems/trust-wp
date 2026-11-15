//@ expect: reject
//@ mechanism: admission gate treats a closure type as library-semantic only when its captures are; a closure capturing a local type with a hand-written Clone must not receive the library Option::clone contract
//@ accept-means: the clone of a closure was taken as identical to the original although cloning runs the local S::clone (S(2)), so the cloned closure returns 2
//@ teeth: wp-s38 362032fa+: TRUST_WP_ADMISSION_DUMP shows Clone::clone admitted=false with BOUND Clone on Closure[.., (S,)]; a whole-place capture (let r = &s inside) is required, since move || s.0 captures only the u32 field
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S(pub u32);
impl Clone for S {
    fn clone(&self) -> S { S(2) }
}

// FALSE: the closure captures the WHOLE s (a reference to s is taken inside),
// so cloning the closure runs S::clone and the clone returns 2.
#[ensures(result == 1u32)]
pub fn f() -> u32 {
    let s = S(1);
    let c = move || { let r = &s; r.0 };
    let o = Some(c);
    let o2 = o.clone();
    match o2 { Some(g) => g(), None => 1 }
}
