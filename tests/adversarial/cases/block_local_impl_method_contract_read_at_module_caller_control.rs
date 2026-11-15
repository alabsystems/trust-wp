//@ expect: verify
//@ mechanism: TRUE twin of block_local_impl_method_contract_read_at_module_caller.rs: `caller` claims
//@ mechanism: `result@ == 0`, which `S::g`'s contract gives with the block's `k` (0). Both the callee's
//@ mechanism: verification and its contract read at the module-scope call site resolve `k` in the block
//@ mechanism: around `g` (D-195), so both verify.
//@ teeth: over-refusal control. MEASURED: with the module lookup alone (the campaign tip this branch was
//@ teeth: built on) `host::<impl S>::g` and `caller` are both FAILED; with D-195 both verify.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub struct S;

pub fn host() {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    impl S {
        #[ensures(result@ == k())]
        pub fn g(&self) -> u32 {
            0
        }
    }
}

// RIGHT: `S::g` returns 0, the block's `k`.
#[ensures(result@ == 0)]
pub fn caller(s: &S) -> u32 {
    s.g()
}
