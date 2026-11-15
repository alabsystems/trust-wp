//@ expect: verify
//@ mechanism: isolating twin of named_trait_call_block_local_trait_shadow, differing in the claim alone: `!Other::holds(s)` in the contract of `inner`, declared in `host`'s body, where the block's own trait `Other` has `holds` at `S` `false` and the crate root's `Other` has it `true`. Rust reads `Other` as the block's trait, so the claim holds; a call bound to the root's trait would refute it.
//@ teeth: over-refusal control for D-208: refused (`unknown`) under D-160's refusal of a named-trait call inside a body, verified once the qualifier is read through the block scopes (D-195).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

pub struct S;

impl Other for S {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub fn host() {
    trait Other {
        #[logic]
        fn holds(self) -> bool;
    }
    impl Other for S {
        #[logic(open)]
        fn holds(self) -> bool {
            false
        }
    }
    #[ensures(!Other::holds(s))]
    fn inner(s: S) {}
    inner(S)
}
