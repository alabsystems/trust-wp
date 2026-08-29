// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// cc/seq.rs `g`: symbolic Seq subsequence length postconditions.
///
/// Models the simplest postcondition from cc/seq.rs:
///   `#[requires(s.len() >= 1)]`
///   `#[ensures(s[0..1].len() == 1)]`
///
/// The contract parser desugars `s[0..1]` into `s.subsequence(0, 1)`.
/// With the AUFLIA pipeline, verifying `subsequence(s, 0, 1).len() == 1`
/// given `s.len() >= 1` should be UNSAT (verified) since the subsequence
/// shape constraints set `new_len = max(0, to - from) = max(0, 1) = 1`.
///
/// Part of #2463.
#[test]
#[timeout(30000)]
fn test_cc_seq_g_subsequence_len_postcondition_pipeline() {
    // requires: s.len() >= 1
    let req = ge(method_call(var("s"), "len", vec![]), int(1));

    // ensures: s.subsequence(0, 1).len() == 1  (desugared from s[0..1].len() == 1)
    let subseq = method_call(var("s"), "subsequence", vec![int(0), int(1)]);
    let ens = eq(method_call(subseq, "len", vec![]), int(1));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "s[0..1].len() == 1 given s.len() >= 1 should verify, got {result:?}"
    );
}
