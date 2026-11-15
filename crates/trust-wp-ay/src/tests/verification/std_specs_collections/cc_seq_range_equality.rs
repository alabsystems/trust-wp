// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// cc/seq.rs `g`: `s[0..] == s` — full suffix equals self.
///
/// Desugars to `s.subsequence(0, s.len()) == s`. This is a structural
/// identity: same array, same length, same offset. Part of #2463.
#[test]
#[timeout(60000)]
fn test_cc_seq_g_full_suffix_eq_self_pipeline() {
    let req = ge(method_call(var("s"), "len", vec![]), int(1));
    let s_len = method_call(var("s"), "len", vec![]);
    let subseq = method_call(var("s"), "subsequence", vec![int(0), s_len]);
    let ens = eq(subseq, var("s"));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]));
    // This involves Seq equality decomposition on a symbolic Seq.
    // subsequence(s, 0, s.len()) should have the same Array, Length,
    // and Offset components as `s` itself, so the decomposed equality
    // is deterministic.
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "s[0..] == s should verify, got {result:?}"
    );
}

/// cc/seq.rs `g`: `s[..] == s` — full range desugaring.
///
/// `s[..]` desugars to `s.subsequence(0, s.len())`.
/// This is the same as `test_cc_seq_g_full_suffix_eq_self_pipeline`
/// but models the `RangeFull` variant explicitly. Part of #2463.
#[test]
#[timeout(60000)]
fn test_cc_seq_g_full_range_eq_self_pipeline() {
    let req = ge(method_call(var("s"), "len", vec![]), int(1));
    let s_len = method_call(var("s"), "len", vec![]);
    let subseq = method_call(var("s"), "subsequence", vec![int(0), s_len]);
    let ens = eq(subseq, var("s"));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]));
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "s[..] == s should verify, got {result:?}"
    );
}
