//@ expect: reject
//@ mechanism: a logic function returns `Some(x)` on one branch and its `Option<Int>` parameter on the other, and claims `result != None`. The datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) is written for a body MIR unwrapped from its constructor: when a postcondition compares `result` with a constructor, the body is wrapped in one (`encode_branch_as_datatype`), and a body that is already a value of the datatype (the parameter branch) is wrapped too, so both branches are read as `Some(..)` and the solver PROVES the false postcondition; the crate is rejected only because mandatory strict certification cannot certify that proof (`postcondition unverified (proof-trusted)`), a verdict that turns on the certificate's shape, not on the contract.
//@ fixed-by: D-165
//@ accept-means: a logic function is credited with a postcondition its body violates, and callers are handed it as a fact.
//@ WHY IT IS FALSE: `caller(1, None)` is `None`.
//@ teeth: MEASURED at the campaign tip: the solver proves the postcondition and strict certification withholds it (`creusot_test::caller postcondition unverified (proof-trusted)`), so the declared refusal, a counterexample, is not what rejects it. At D-165: `trust-wp: creusot_test::caller postcondition FAILED (logic postcondition)`.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result != None)]
pub fn caller(x: Int, o: Option<Int>) -> Option<Int> {
    if x == 0 { Some(x) } else { o }
}
