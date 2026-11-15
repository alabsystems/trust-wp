//@ expect: reject
//@ mechanism: a clause of a function declared in a block names a logic function declared in that
//@ mechanism: same block, and the crate root declares another logic function of the same name. Rust
//@ mechanism: resolves `k()` in `inner`'s contract to the block's `k` (0): an item in a block shadows
//@ mechanism: the module's. trust-wp's logic-function resolver looks a bare name up among the
//@ mechanism: children of the owner's MODULE (`Resolver::owner_module` skips every enclosing block),
//@ mechanism: so it reads `k` as the root's `k` (10), and `inner`, which returns 10, is verified
//@ mechanism: against a contract it violates. The twin that returns 0 and honours the contract is
//@ mechanism: refuted (block_local_logic_fn_name_honoured_control.rs, xfail): the verdicts are
//@ mechanism: inverted. Sibling spellings: block_local_module_path_resolved_in_module_granted.rs (a
//@ mechanism: path through a module declared in the block), closure_contract_block_local_logic_fn_granted.rs
//@ mechanism: (a closure's contract) and trait_inherited_clause_block_local_name_granted.rs (a trait
//@ mechanism: declared in the block, whose inherited clause D-110 restates in the "trait's scope").
//@ fixed-by: D-174 — an item declared in a body that encloses the owner withholds the module's answer
//@ fixed-by: for its name (`shadowed_by_body_item`), so `k` names two definitions and the colliding
//@ fixed-by: call is refused. Resolving block scopes as Rust does, which would prove the honoured
//@ fixed-by: twin, is not done.
//@ refused-with: names one of several definitions
//@ accept-means: `inner` claims `result@ == k()` with the block's `k` (0) and returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`) without D-174's check, before D-110
//@ teeth: and after it alike; with it, `host::inner` is refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub fn host() -> u32 {
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
