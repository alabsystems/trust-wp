//@ expect: verify
//@ mechanism: isolating twin of named_trait_call_block_use_rename_callee_contract.rs, differing in
//@ mechanism: `caller`'s claim alone: `!result`, which holds where `g`'s text names `other::Tr2` (the
//@ mechanism: block's renaming import), as Rust reads it, and is refuted on the root's `Other`.
//@ teeth: over-refusal control for D-208 (2) in callee clause text: verified at wp-s139 236a48a4,
//@ teeth: refused (`unknown`) at the campaign tip 2d7d2634.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

#[derive(Clone, Copy)]
pub struct S;

impl Other for S {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub mod other {
    use creusot_std::prelude::*;
    pub trait Tr2 {
        #[logic]
        fn holds(self) -> bool;
    }
    impl Tr2 for super::S {
        #[logic(open)]
        fn holds(self) -> bool {
            false
        }
    }
}

pub fn host() -> bool {
    use other::Tr2 as Other;
    #[ensures(result == Other::holds(s))]
    fn g(s: S) -> bool {
        let _ = s;
        false
    }
    #[ensures(!result)]
    fn caller(s: S) -> bool {
        g(s)
    }
    caller(S)
}
