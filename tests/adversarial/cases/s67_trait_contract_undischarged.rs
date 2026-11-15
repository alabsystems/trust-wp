//@ expect: reject
//@ mechanism: a generic caller kept a trait method's contract that the impl never discharged
//@ fixed-by: s67 (wp-s67, trait-contract credit ledger + demotion); D-86 (the withdrawal walks the call graph)
//@ accept-means: `gen_read` verified `result` for EVERY `T: Rd` on the strength of a trait contract this crate's only impl refuted; `go` then returns false while claiming true.
//@ teeth: without the credit ledger `gen_read verified ✓` and `go verified ✓` stand while `<W as Rd>::rd trait refinement FAILED ✗`. With the ledger alone `gen_read` is withdrawn and `go`, which took no trait grant of its own, keeps its credit one ordinary call away; the call-graph walk withdraws both, and neither may be declared.
//@ also-verified: <W as Rd>::rd
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

// A trait clause with no type suffix and no method call: nothing in it is
// scope-dependent, so the refinement checker has no excuse to refuse.
pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

// The impl declares its OWN, strictly weaker contract, so it inherits nothing
// and its body obligation (`true`) is trivially discharged. Only the refinement
// goal stands between the trait's `result` and a body that returns `false`.
impl Rd for W {
    #[ensures(true)]
    fn rd(&self) -> bool {
        false
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}
