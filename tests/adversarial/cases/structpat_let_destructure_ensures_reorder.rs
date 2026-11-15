//@ expect: reject
//@ verdict: failed
//@ fixed-by: 0d0aaba9
//@ mechanism: `let S { a: aa, b: _bb } = s;` in specification text is desugared by the
//@ mechanism: contract parser itself (contract_parser/unspanned/blocks.rs desugar_let_pattern
//@ mechanism: -> desugar_field_bindings) into positional `__trust_wp_tuple_get_<i>` reads,
//@ mechanism: with `i` the WRITTEN position. The constructor name is discarded there, so no
//@ mechanism: named-field metadata exists for the placement pass or the encoder gate to see.
//@ accept-means: a binding denotes whichever field was declared at its written position,
//@ accept-means: not the field it names; the contract is discharged against the wrong value.
//@ teeth: MEASURED on the merged tip 4e4613be (TRUST_WP_HARNESS_PROFILE=debug, ay a9c919158a):
//@ teeth: ACCEPTED, exit 0 — a live false accept. Its true control (the `_control` twin) FAILED on
//@ teeth: the same binary: the pair shows written order decided the verdict.
extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires(s.a@ == 5 && s.b@ == 0)]
#[ensures({ let S { a: aa, b: _bb } = s; result@ == aa@ })]
pub fn g(s: S) -> u32 { match s { S { b, a: _a } => b } }
