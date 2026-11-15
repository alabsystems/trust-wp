//@ expect: reject
//@ verdict: failed
//@ mechanism: `Other::holds(s)` in the contract of `inner`, a function declared in `host`'s body, where the block declares its own trait `Other` with an impl for `S`: Rust reads `Other` as the block's trait, whose `holds` at `S` is `false`. The crate root declares another trait `Other` whose `holds` at `S` is `true`. A call through a named trait is looked up among that trait's implementations (D-160), and the trait is found by the module lookup, which skips every enclosing block (the defect of block_local_logic_fn_name_resolved_in_module_granted.rs): it finds the root's `Other` and would bind its `holds`. Inside a body the named trait is not known, and the call is refused.
//@ fixed-by: D-160 (a call through a named trait written inside a body is refused; before the narrowing, the lookup over every definition of `holds` saw both impls at `S` and refused)
//@ accept-means: a call through a named trait inside a body was bound to a module-level trait of the same name, and `inner` was credited on it.
//@ WHY IT IS FALSE: in `inner`'s contract `Other` is the block's trait, and `<S as Other>::holds` there is `false`, so `inner`'s postcondition is `false`. Creusot's `vc_inner` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, `host::inner verified ✓`, with the body refusal knocked out of the named-trait lookup.
//@ fixed-by: D-208 — the body refusal is lifted: the qualifier `Other` is read through the block scopes around `inner`'s clause (D-195), which find the block's own trait, and `inner` is refuted (`host::inner FAILED`) on its `holds`, `false`; rustc's confirmation (D-163) stands behind the reading.
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
    // WRONG: here `Other` is the block's trait, whose `holds` at `S` is false.
    #[ensures(Other::holds(s))]
    fn inner(s: S) {}
    inner(S)
}
