//@ expect: reject
//@ mechanism: `host`'s body declares a logic function `k` (10), and a nested block of it declares
//@ mechanism: another `k` (0) beside `inner`, whose contract names `k()`: Rust resolves it to the
//@ mechanism: nested block's `k`. rustc prints both as `host::k`, and every identity table (the unique
//@ mechanism: id, the id -> `DefId` map, the definition list) is keyed by that path, so the id the
//@ mechanism: block lookup would map the nested `k` to stands for either definition. Such an id is
//@ mechanism: refused wherever a resolution would produce it.
//@ fixed-by: not a defect at the head that committed it (the module lookup could not reach a block
//@ fixed-by: item): the guard case of the ambiguous-path refusal the block lookup needs.
//@ accept-means: `inner` claims `result@ == k()` with the nested block's `k` (0) and returns 10, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED with the ambiguous-path refusal disabled by a local knob: ACCEPTED at exit 0
//@ teeth: (`host::inner verified ✓`, the shared id read as `host`'s `k`); with it, `unknown` (the call
//@ teeth: names one of several definitions).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 10 }
    }
    {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
        #[ensures(result@ == k())]
        fn inner() -> u32 {
            10
        }
        inner()
    }
}
