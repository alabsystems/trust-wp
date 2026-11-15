//@ expect: reject
//@ mechanism: D-110 restates an inherited clause as the trait method's grant "resolved in the trait's
//@ mechanism: scope", on the premise that grant and obligation then read one resolved text. Here the
//@ mechanism: trait is declared in `host`'s block, and its clause `result@ == k()` names the logic
//@ mechanism: function declared in that block (0); the crate root declares another `k` (10). The
//@ mechanism: resolver takes the trait method's MODULE for its scope (`Resolver::owner_module` skips
//@ mechanism: blocks), so the one text both sides read is the root's `k`: W's impl, which returns 10,
//@ mechanism: discharges it and is credited against the contract Rust gives it, which it violates. The
//@ mechanism: refinement check's scope closure refuses the pair (`names call k(..), which cannot be
//@ mechanism: resolved in the clause's own scope`), which keeps the crate from exiting 0; D-110 and
//@ mechanism: D-112 skipped that closure for every inherited contract and the run exited 0, so D-113
//@ mechanism: skips it only for a trait declared directly in a module. The impl's credit is false
//@ mechanism: either way: the resolver defect is block_local_logic_fn_name_resolved_in_module_granted.rs.
//@ fixed-by: D-174 — the impl method is nested in `host`'s body, which declares `k`, so the module's
//@ fixed-by: answer is withheld and the inherited clause's `k` names two definitions: the impl is
//@ fixed-by: refused, not credited. D-113 keeps the crate from exiting 0 either way.
//@ refused-with: names one of several definitions
//@ accept-means: `<host::W as host::Rd>::rd` claims `result@ == k()` with the block's `k` (0) and returns 10; ACCEPTED means the crate exits 0 on that credit.
//@ teeth: MEASURED before D-110: rejected (`unknown`) by the refinement refusal, with `<host::W as host::Rd>::rd verified ✓` already printed. At D-110/D-112: ACCEPTED at exit 0. At D-113: rejected as before D-110, the impl still credited (the per-function gate reports it). With D-174: rejected, the impl refused and credited nothing. The isolating twin trait_inherited_clause_block_local_name_honoured_twin.rs (returns 0) is refuted without D-174 and refused with it (xfail).
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
    trait Rd {
        #[ensures(result@ == k())]
        fn rd(&self) -> u32;
    }
    struct W;
    // No clauses of its own: inherits `result@ == k()`.
    impl Rd for W {
        fn rd(&self) -> u32 {
            10
        }
    }
    W.rd()
}
