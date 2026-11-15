//@ expect: verify
//@ mechanism: logic-fn identity — logic fn with an argument (`sq`) defined in two modules with different bodies (definition order ab)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: n/a (control): the true claim about the resolved definition must verify
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn sq(x: Int) -> Int { pearlite!{x * x} }
    pub fn h() { proof_assert!(sq(3) == 9); }
}
pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn sq(x: Int) -> Int { pearlite!{x + x} }
}
