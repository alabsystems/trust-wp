//@ expect: verify
//@ xfail: `unknown (proof-trusted)`: ay answers unsat, and strict certification rejects the proof on a `Generic` theory lemma, the discriminant reasoning that rules the arm out. The same match over two locals (`let a = Some(42); let b = Some(43); match (&a, &b)`) is capped the same way, so the promoted's value is no longer what blocks it: the translation moved this from `refutation withheld: solver evidence was unknown` to the strict-certification bucket.
//@ mechanism: a promoted constant CTFE cannot hand back as a scalar or a newtype (`&Some(42)`, `&(3, 4)`) is read off the promoted's own MIR body by the primary extractor (`translate_promoted_body`), and kept only when CTFE evaluates the promoted, the extraction marked nothing it could not model, and the value is closed (no placeholder variable, whose spelling is derived from the promoted body's local indices and would name one of the enclosing function's values).
//@ mechanism: control: `match (&Some(42), &Some(43))` never takes its `(None, None)` arm. The shape of the Creusot row lang/promoted_constants.rs (`promoted_none`). Twin of promoted_const_match_arm_reachable.rs.
//@ accept-means: n/a (control) — this contract is TRUE; an XPASS here means the strict-certification gap closed.
//@ teeth: n/a — over-refusal control; xfail (see xfail reason).
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn promoted_none() -> Option<i32> {
    let ix = Some(0);
    match (&Some(42), &Some(43)) {
        (None, None) => panic!(),
        _ => (),
    }
    ix
}
