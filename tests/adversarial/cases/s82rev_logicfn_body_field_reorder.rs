//@ expect: reject
//@ mechanism: a named-field pattern inside a LOGIC FUNCTION BODY never reaches
//@ mechanism: `place_named_fields`. `logic_fn_catalog.rs:100` mirrors the contract
//@ mechanism: rewrites over `LogicFnDef` bodies but NOT the placement one, so the
//@ mechanism: `{a,b}` metadata survives to the encoder and `normalize_constructor_name`
//@ mechanism: (trust-wp-ay .../match_enc/switch_target/mod.rs:25) binds the
//@ mechanism: sub-patterns POSITIONALLY, in SOURCE order.
//@ mechanism: Here `pick` names field `a` while `g` returns field `b`. Written in
//@ mechanism: declaration order the identical program FAILS — the verdict is decided
//@ mechanism: by the order the two fields were written in.
//@ accept-means: a logic function reads a different field than the one it names, so
//@ accept-means: any contract resting on it is discharged against the wrong value.
extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[logic(open)]
pub fn pick(s: S) -> Int { pearlite! { match s { S { a: aa, b: _bb } => aa@ } } }

#[requires(pick(s) == 5)]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b, a: _a } => b } }
