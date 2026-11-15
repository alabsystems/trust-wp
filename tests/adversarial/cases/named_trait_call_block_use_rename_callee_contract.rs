//@ expect: reject
//@ verdict: failed
//@ also-verified: host::g
//@ mechanism: D-208 (2) in a callee's contract TEXT through a renaming import: `host`'s block writes
//@ mechanism: `use other::Tr2 as Other;`, and `g`, declared in that block, claims
//@ mechanism: `result == Other::holds(s)`. Rust reads `Other` there as `other::Tr2`, whose `holds` at
//@ mechanism: `S` is `false`; the crate root's own trait `Other` has `holds` at `S` `true`. `g` returns
//@ mechanism: `false`, honouring Rust's reading. `caller`, in the same block, returns `g(s)` and claims
//@ mechanism: `result`: false by Rust's reading, true if `g`'s text named the root's `Other`. The text
//@ mechanism: resolver reads the qualifier through the block scopes around `g`
//@ mechanism: (`qualifier_in_scope`, D-195's lookup of a single import), so `caller` is refuted.
//@ fixed-by: D-208 — a named trait inside a body is read through the block scopes, in callee clause
//@ fixed-by: text as in the owner's reading; at the campaign tip it was refused (D-160 item 2).
//@ accept-means: `caller` is credited with `result` on the root trait's `holds`, where Rust reads
//@ accept-means: `other::Tr2::holds`, `false`.
//@ teeth: MEASURED at wp-s139 236a48a4: `host::caller FAILED ✗ (postcondition)`, `host::g verified ✓`.
//@ teeth: The isolating twin named_trait_call_block_use_rename_callee_contract_true_control.rs differs
//@ teeth: in `caller`'s claim alone and verifies there. At the campaign tip 2d7d2634 both are refused
//@ teeth: (`unknown`: `Other::holds` matches several impls).
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
    // WRONG: `g(s)` is `other::Tr2::holds(s)`, false.
    #[ensures(result)]
    fn caller(s: S) -> bool {
        g(s)
    }
    caller(S)
}
