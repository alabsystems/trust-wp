//@ expect: verify
//@ mechanism: the boundary of glob_may_import: the owner's body globs a module WITHOUT a `k`,
//@ mechanism: so the clause's `k` is still the crate root's `use a::k` and resolves to it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p }
}
pub mod c {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p + 2 }
}
pub mod d {
    pub fn unrelated() {}
}
use a::k;

#[ensures(result@ == k(x@))]
pub fn g(x: u32) -> u32 {
    #[allow(unused_imports)]
    use crate::d::*;
    x
}
