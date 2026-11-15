//@ expect: reject
//@ mechanism: `A::m(s)` in `g`'s `ensures`, with `pub type A = U;` and `U`'s inherent PROGRAM
//@ mechanism: associated function `m(_x: S) -> u32` (0): Rust reads the path through the alias as
//@ mechanism: `U::m(s)`, a program function, which Creusot refuses in a specification. Every local
//@ mechanism: logic `m` is a method (`S::m`, 10), so the family dispatches on its receiver
//@ mechanism: (`dispatches_on_receiver`). `Resolver::resolve_prefix` maps an alias to no target
//@ mechanism: (`path_target`), and `resolve_call_name_unchecked`'s `self.resolve_prefix(prefix)?`
//@ mechanism: answers "unresolved", which leaves the call under its written name: D-196 says a
//@ mechanism: method-style call is never left there, because the encoder dispatches every colliding
//@ mechanism: name it receives on its first argument's sort. The encoder does: `A::m(s)` is read as
//@ mechanism: `S::m(s)` (10), whose per-member `receiver_dispatch` (`method_lookup::selects_only`)
//@ mechanism: counts methods only and never sees `U`'s associated function. D-136's check of a
//@ mechanism: specification's calls compares the spelling's last segment with the resolved item's
//@ mechanism: name (`m` and `m`) and passes it. `g`, which returns 10, is credited.
//@ mechanism: Siblings: block_type_alias_path_call_to_program_assoc_fn_read_as_logic_method_granted.rs
//@ mechanism: (the alias declared in a block, D-195's scope) and
//@ mechanism: callee_contract_type_alias_path_call_read_as_logic_method_granted.rs (a caller's credit).
//@ fixed-by: D-209 — an unplaced prefix of a method-style path call is refused (`resolve_call_name_unchecked`).
//@ accept-means: `g` claims `result == A::m(s)` where Rust's `A::m` is `U`'s program function,
//@ accept-means: returns 10, and is credited on `S::m` (10); the crate exits 0.
//@ teeth: MEASURED at wp-s139 236a48a4 and at the campaign tip 2d7d2634: ACCEPTED, exit 0
//@ teeth: (`g verified ✓`).
//@ teeth: With D-209: refused (`g error: ... __lfidU__.._N.._ was not resolved`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;
impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

pub struct U;
impl U {
    pub fn m(_x: S) -> u32 {
        0
    }
}

pub type A = U;

// WRONG: `A::m` is `U`'s program function, not `S::m`.
#[ensures(result == A::m(s))]
pub fn g(s: S) -> u32 {
    let _ = s;
    10
}
