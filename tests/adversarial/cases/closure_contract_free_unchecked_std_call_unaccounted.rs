//@ expect: reject
//@ verdict: unknown
//@ mechanism: a clause-free body's call through `Fn::call` on a local closure is accounted for
//@ mechanism: panic purposes only when that closure has a user spec, i.e. is its own verification
//@ mechanism: target (`fn_trait_call_local_closure` in `unchecked_panic_sites`). This closure has
//@ mechanism: none: it is a target of nothing, and its body calls a std function whose spec states
//@ mechanism: no panic precondition, so the transparent-closure precondition the call site
//@ mechanism: discharges holds for every argument and the only thing between `f` and `verified` is
//@ mechanism: the site staying unaccounted. Most contract-free closures that panic (`panic!`, an index,
//@ mechanism: `unwrap`) are already refused upstream, because their body WP is withheld and the
//@ mechanism: call's `precondition` stays uninterpreted; this shape is the one that is not.
//@ fixed-by: D-103 — a Fn-trait call enters the closure, held to the local-callee rule.
//@ accept-means: crediting every local closure as a checked callee lets any panic hidden in a
//@ accept-means: contract-free closure's std calls escape the only verdict that could report it.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics; `c(usize::MAX)` builds a `Vec<()>` of `usize::MAX` elements, its
//@ WHY THE CONTRACT IS FALSE: capacity, and pushing one more panics with "capacity overflow" in every
//@ WHY THE CONTRACT IS FALSE: build profile.
//@ teeth: MEASURED as ACCEPTED, exit 0, "f verified ✓, 1 verified, 0 failed", with a local env
//@ teeth: knob crediting every site that resolves to a local closure regardless of its spec;
//@ teeth: `unknown (partial: panic paths unchecked (call to std::ops::Fn::call))` without it.
//@ note: the panic is a zero-sized push because `Vec::push` is a std call whose spec states no
//@ note: panic precondition (zst_vec_push_len_overflow_std_spec_silent). A std call whose spec owes
//@ note: its panic (D-121) is charged at the call through the closure's body WP, before the
//@ note: account this case isolates.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = |n: usize| -> usize {
        let mut v: Vec<()> = vec![(); n];
        v.push(());
        v.len()
    };
    let _r = c(usize::MAX);
}
