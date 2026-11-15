//@ expect: verify
//@ xfail: a wrong reject, `p unknown (refutation withheld)`. `x.is_some()` reads `x` before `match x`
//@ xfail: does: the encoder declares `x` at its annotation's opaque `Option` sort where the precondition
//@ xfail: first reads it, and the match upgrades it to the `OptionInt` datatype under a fresh symbol
//@ xfail: (`PhantomVariableUpgrade`), so the precondition and the arms speak of two unrelated constants.
//@ xfail: The solver's model (`x = None` beside `x.is_some()`) is no execution; D-218 withholds it.
//@ xfail-verdict: unknown
//@ mechanism: A std `Option` read through its opaque sort before a match takes it apart.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: OPEN — needs the reads linked where no earlier read is stale; the link D-218 refuses
//@ fixed-by: lets stale reads prove arms (closure_precondition_option_match_on_reassigned_param_read_at_entry.rs).
//@ teeth: control — `p FAILED` (counterexample `x = None`) before D-218, withheld with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x.is_some())]
#[ensures(match x { Some(_) => true, None => false })]
pub fn p(x: Option<u32>) {}
