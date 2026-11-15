//@ expect: reject
//@ mechanism: logic-fn identity — recursive open logic fn k in two modules; bare recursive call resolved in the owner module (definition order ba)
//@ fixed-by: s35 logic-fn identity (type-directed receiver resolution, generic markers at call sites)
//@ accept-means: a clause was checked against a definition Rust would not select for that type
//@ teeth: rejected on fd7534d only in this definition order; its twin order was accepted (see s35 progress.md)
//@ also-verified: creusot_test::a::k, creusot_test::b::k
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod b { use creusot_std::prelude::*;
  #[logic(open)] #[variant(n)] #[requires(n >= 0)] pub fn k(n: Int) -> Int { pearlite!{ if n == 0 { 1 } else { k(n - 1) } } } }
pub mod a { use creusot_std::prelude::*;
  #[logic(open)] #[variant(n)] #[requires(n >= 0)] pub fn k(n: Int) -> Int { pearlite!{ if n == 0 { 0 } else { k(n - 1) } } }
  pub fn h() { proof_assert!(k(2) == 1); } }
