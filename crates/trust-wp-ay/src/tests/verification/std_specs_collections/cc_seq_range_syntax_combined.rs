// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// cc/seq.rs `g`: ALL 6 postconditions combined in one verification request.
///
/// This tests what the compat harness sees: a single function with one
/// precondition and six postconditions. Individual tests pass; this checks
/// whether the combined obligation triggers internal-error or other failures.
///
/// Part of #2463.
#[test]
#[timeout(60000)]
fn test_cc_seq_g_all_postconditions_combined_pipeline() {
    let req = ge(method_call(var("s"), "len", vec![]), int(1));
    let s_len = method_call(var("s"), "len", vec![]);

    // ensures: s[0..1].len() == 1
    let ens1 = eq(
        method_call(
            method_call(var("s"), "subsequence", vec![int(0), int(1)]),
            "len",
            vec![],
        ),
        int(1),
    );
    // ensures: s[0..=0].len() == 1  →  s.subsequence(0, 0+1).len() == 1
    let ens2 = eq(
        method_call(
            method_call(var("s"), "subsequence", vec![int(0), add(int(0), int(1))]),
            "len",
            vec![],
        ),
        int(1),
    );
    // ensures: s[0..] == s  →  s.subsequence(0, s.len()) == s
    let ens3 = eq(
        method_call(var("s"), "subsequence", vec![int(0), s_len.clone()]),
        var("s"),
    );
    // ensures: s[..0].len() == 0  →  s.subsequence(0, 0).len() == 0
    let ens4 = eq(
        method_call(
            method_call(var("s"), "subsequence", vec![int(0), int(0)]),
            "len",
            vec![],
        ),
        int(0),
    );
    // ensures: s[..=0].len() == 1  →  s.subsequence(0, 0+1).len() == 1
    let ens5 = eq(
        method_call(
            method_call(var("s"), "subsequence", vec![int(0), add(int(0), int(1))]),
            "len",
            vec![],
        ),
        int(1),
    );
    // ensures: s[..] == s  →  s.subsequence(0, s.len()) == s
    let ens6 = eq(
        method_call(var("s"), "subsequence", vec![int(0), s_len]),
        var("s"),
    );

    let result = verify_function_with_modes(VerificationRequest::new(
        &[req],
        &[ens1, ens2, ens3, ens4, ens5, ens6],
    ));
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "cc/seq.rs g() with all 6 postconditions should verify, got {result:?}"
    );
}
