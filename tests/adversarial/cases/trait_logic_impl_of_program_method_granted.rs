//@ expect: reject
//@ verdict: error
//@ refused-with: Expected `rd` to be a program function as specified by the trait declaration
//@ mechanism: a `#[logic]` impl of a contracted PROGRAM trait method owes the trait contract and
//@ mechanism: was never asked for it. The contract loop classified `<W as Rd>::rd` as a logic function
//@ mechanism: (`is a logic function (definition registered)`) and moved on without `end_item`, so the
//@ mechanism: ledger recorded nothing, and `record_unexamined` did not either, because the loop did
//@ mechanism: reach it. The refinement pass then compared the impl's contract with the trait's, and
//@ mechanism: the impl inherited the trait's clauses verbatim, so that goal was a tautology. Nothing
//@ mechanism: checked the body `false` against the inherited `result`. `go` is pinned to W's impl and
//@ mechanism: `gen_read` may run any impl; both kept the grant.
//@ fixed-by: D-110 (a logic function cannot implement a program trait method, as Creusot's `can_implement` refuses it; the contract loop's logic arms settle the trait contract they owe)
//@ accept-means: `go` claims `result`; in the logic model W's `rd` is `false`, and at run time the call reaches the logic function's erased body, which is `unreachable!()`. `gen_read` claims `result` for every `T: Rd`, W included. Creusot rejects the impl outright: a program trait item cannot be implemented by a logic function.
//@ teeth: MEASURED at the parent commit: ACCEPTED with exit 0, `gen_read verified ✓` and `go verified ✓`, and no withdrawal; the same crate with the logic body `true` printed the identical lines. With the refusal knocked out by a local knob, the ledger arm alone withdraws both: `<W as Rd>::rd` is recorded as a logic function, which cannot implement a program trait method. trait_logic_impl_of_program_method_program_twin.rs, the impl as a program `fn` returning true, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

pub struct W;

// Inherits `result`; a logic body that returns false never discharges it.
impl Rd for W {
    #[logic(open)]
    fn rd(&self) -> bool {
        pearlite! { false }
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    W.rd()
}
