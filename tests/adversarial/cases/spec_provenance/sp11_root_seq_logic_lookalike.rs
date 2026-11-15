//@ expect: reject
//@ mechanism: crate-root logic type `Seq` with a local logic `len`; encoder keys Seq sort/len by bare name
//@ accept-means: a local lookalike Seq in logic received the spec library's Seq length axioms (real -1)
//@ verdict: error
//@ refused-with: creusot_test::g postcondition FAILED (logic postcondition)
//@ teeth-credit: Re-pinned 2026-09-18 (wp-s69, validated refutations). The s55-era line was
//@ teeth-credit: `g postcondition unverified (refutation withheld: ..)`: the structural precheck
//@ teeth-credit: refuted `result >= 0` (len is -1) without a model and the gate withheld it. The
//@ teeth-credit: solver now produces the model, so the logic-postcondition check reports its own
//@ teeth-credit: named line above (warning disposition, counted as an unverified axiom: exit 2).
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (trust-wp's logic-postcondition check does not certify the local Seq lookalike's postcondition, so the lookalike never receives the spec library's Seq axioms; the run ends as verdict=error (unverified axiom, exit 2), so that line is what is pinned); measured at edition 2024. Re-pinned 2026-09-14 (wp-s55): the line used to read `postcondition FAILED (logic postcondition)`, but that verdict carried NO validated counterexample model — `ay_result=none`, no provenance — so the refutation-authority gate now withholds it and reports the honest `unverified (refutation withheld: ...)`. The teeth are unchanged: `g`'s postcondition is still not certified, which is the whole mechanism; only the claim that a counterexample had been computed is gone. `(refutation withheld:` is kept in the pin so a plain solver timeout, which also prints `postcondition unverified`, cannot satisfy it.
use creusot_std::prelude::*;
pub struct Seq<T>(pub Option<T>);
impl<T> Seq<T> {
    #[logic(open)]
    pub fn len(self) -> Int { -1 }
}
#[logic(open)]
#[ensures(result >= 0)]
pub fn g(s: Seq<u32>) -> Int { s.len() }
