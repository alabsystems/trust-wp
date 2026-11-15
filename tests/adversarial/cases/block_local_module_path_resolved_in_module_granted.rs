//@ expect: reject
//@ mechanism: the path spelling of block_local_logic_fn_name_resolved_in_module_granted.rs. `inner`'s
//@ mechanism: contract names `m::k()`, where `m` is a module declared in `host`'s block; the crate root
//@ mechanism: declares another module `m` with its own `k`. Rust resolves the first segment in the
//@ mechanism: block, so the clause means the block's `m::k` (0). The resolver looks `m` up among the
//@ mechanism: owner's module's children (`Resolver::resolve_prefix`), finds the root's `m`, and
//@ mechanism: `inner`, which returns 10, is verified against the root's `m::k` (10).
//@ fixed-by: D-174 — the block's `mod m` withholds the module's answer for the qualifier `m`, so
//@ fixed-by: `m::k` names two definitions and the colliding call is refused.
//@ refused-with: names one of several definitions
//@ accept-means: `inner` claims `result@ == m::k()` with the block's module (0) and returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`) without D-174's check, before D-110
//@ teeth: and after it alike; with it, `host::inner` is refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
}

pub fn host() -> u32 {
    mod m {
        use creusot_std::prelude::*;
        #[logic(open)]
        pub fn k() -> Int {
            pearlite! { 0 }
        }
    }
    #[ensures(result@ == m::k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
