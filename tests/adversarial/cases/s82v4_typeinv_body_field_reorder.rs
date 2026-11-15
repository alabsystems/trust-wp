//@ expect: reject
//@ verdict: failed
//@ mechanism: a reordered named-field pattern inside a TYPE INVARIANT BODY. An
//@ mechanism: `impl Invariant for T` body is parsed by logic/type_transforms.rs and registered
//@ mechanism: with the encoder as a defining axiom. `type_invariants::rewrite_invariant_def_named_fields`
//@ mechanism: reached the placement pass only for `DefKind::Struct` types AND only for bodies
//@ mechanism: containing a field ACCESS, so a body whose only named-field construct is a match
//@ mechanism: PATTERN was never placed — the `{a,b}` metadata reached the encoder and the
//@ mechanism: sub-patterns were bound POSITIONALLY in SOURCE order.
//@ accept-means: a type invariant constrains a different field than the one it names, so every
//@ accept-means: function that assumes the invariant assumes the wrong fact.
//@ WHY THE CONTRACT IS FALSE: the invariant names `a`; `g` returns `b`, which nothing
//@ WHY THE CONTRACT IS FALSE: constrains. `S { b: 0, a: 5 }` satisfies the invariant and
//@ WHY THE CONTRACT IS FALSE: returns 0.
//@ teeth: MEASURED on the s82 v3 head binary (e807b1f014, TRUST_WP_HARNESS_PROFILE=debug):
//@ teeth: ACCEPTED, exit 0 — a live false accept, found by the v3 reviewer as probe t04. After
//@ teeth: the v4 fix: failed, exit 1.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub b: u32,
    pub a: u32,
}

impl Invariant for S {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { match self { S { a: aa, b: _bb } => aa@ == 5 } }
    }
}

#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 {
    match s {
        S { b, a: _a } => b,
    }
}
