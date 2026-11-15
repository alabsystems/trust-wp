//@ expect: verify
//@ mechanism: control: a glob import declared in the block brings only `J` into scope, so `K` in the
//@ mechanism: contract still means the root's constant (10), and `inner` returns 10. A refusal of
//@ mechanism: block_glob_import_const_resolved_as_module_const_granted.rs must be keyed on the names
//@ mechanism: the glob actually brings.
//@ fixed-by: n/a (control for block_glob_import_const_resolved_as_module_const_granted.rs; verified
//@ fixed-by: before D-195 and with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const K: u8 = 10;

pub mod other {
    pub const J: u8 = 0;
}

pub fn host() -> u8 {
    #[allow(unused_imports)]
    use crate::other::*;
    #[ensures(result == K)]
    fn inner() -> u8 {
        10
    }
    inner()
}
