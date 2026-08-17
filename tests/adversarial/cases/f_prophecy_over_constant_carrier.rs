//@ expect: reject
//@ mechanism: Final-collapse guard, CONSTANT-carrier arm — `encode_wrapper_rewrite`'s "wrappers
//@ mechanism: are no-ops on literals" arm folded `^<literal>` to the literal. The driver advances
//@ mechanism: a base local through a borrow chain as `Final(<its value expression>)`
//@ mechanism: (mir_analysis/extract/substitution/visitor.rs, #1581), so a local initialised from a
//@ mechanism: constant lowers to `Final(Int(3))`. The sort-based Fix A guard cannot see this shape:
//@ mechanism: a literal's sort is Int/Bool/Float, all of which sort_embeds_mut_ref classifies as
//@ mechanism: pure values, so the collapse was permitted.
//@ fixed-by: tract19 (AYEncoder::refuse_prophecy_over_constant — Fix A constant-carrier arm)
//@ accept-means: `^p == *p` is assertable whenever the borrowed place's value is a constant. Every
//@ accept-means: postcondition about the post-state of such a borrow is then discharged against the
//@ accept-means: PRE-state, i.e. any mutation through the borrow is invisible to the contract.
//@
//@ WHY THE CONTRACT IS FALSE: `touch` writes 99 through the borrow, and `r` expires before the
//@ return, so `x` is 99 at the return. `result@ == 3` is the entry value, and is refutable.
//@ `touch`'s own contract is TRUE and is deliberately an inequality, not an equality on the
//@ prophecy, so the caller's assumed premise (`(^r)@ >= 0`) stays satisfiable and the vacuity
//@ guard never fires — the accept is reached on the goal side, not hidden behind a demotion.
//@ teeth: ★VERIFIED as a LIVE false accept on pristine 4d809ba x ay ba6c479fc, before any fix:
//@ teeth: "trust-wp: prophecy_over_literal_false_accept verified ✓", exit code 0, with
//@ teeth: decisions=0 and the negated postcondition encoded to literal `false`
//@ teeth: ("(assume t0 false)"). This is not a reconstruction — it is the run that found the bug.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// TRUE contract, deliberately not an equality on the prophecy.
#[ensures((^r)@ >= 0)]
fn touch(r: &mut i32) {
    *r = 99;
}

/// FALSE contract: after `touch(r)` and `r`'s expiry, `x` is 99, not 3.
#[ensures(result@ == 3)]
pub fn prophecy_over_literal() -> i32 {
    let mut x = 3i32;
    let r = &mut x;
    touch(r);
    return x;
}
