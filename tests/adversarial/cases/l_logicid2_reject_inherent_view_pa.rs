//@ expect: reject
//@ mechanism: logic-fn identity v2 — singleton inherent A::view answered u.view() inside proof_assert!
//@ fixed-by: s35 logic-fn identity v2 (every local logic def has a unique id; method calls bind only by receiver type)
//@ accept-means: a local logic definition answered a method call on a receiver whose Rust type does not have it
//@ teeth: accepted with exit 0 on wp-campaign 21c018a1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
#[ensures(true)]
pub fn g(u: u32) { proof_assert!(u.view() == 5); }
