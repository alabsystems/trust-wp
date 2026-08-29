// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// cc/seq.rs `g`: `s[..0].len() == 0` — empty prefix subsequence.
///
/// Desugars to `s.subsequence(0, 0).len() == 0`.
/// The subsequence width is `max(0, 0 - 0) = 0`. Part of #2463.
#[test]
#[timeout(30000)]
fn test_cc_seq_g_empty_prefix_len_pipeline() {
    let req = ge(method_call(var("s"), "len", vec![]), int(1));
    let subseq = method_call(var("s"), "subsequence", vec![int(0), int(0)]);
    let ens = eq(method_call(subseq, "len", vec![]), int(0));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "s[..0].len() == 0 should verify, got {result:?}"
    );
}

/// cc/seq.rs `g`: `s[0..=0].len() == 1` — inclusive range desugaring.
///
/// `s[0..=0]` desugars to `s.subsequence(0, 0 + 1)` = `s.subsequence(0, 1)`.
/// Width = max(0, 1 - 0) = 1. Part of #2463.
#[test]
#[timeout(30000)]
fn test_cc_seq_g_inclusive_range_len_pipeline() {
    let req = ge(method_call(var("s"), "len", vec![]), int(1));
    // s[0..=0] → s.subsequence(0, 0 + 1) = s.subsequence(0, 1)
    let subseq = method_call(var("s"), "subsequence", vec![int(0), add(int(0), int(1))]);
    let ens = eq(method_call(subseq, "len", vec![]), int(1));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "s[0..=0].len() == 1 should verify, got {result:?}"
    );
}

/// cc/seq.rs `g`: `s[..=0].len() == 1` — inclusive range-to desugaring.
///
/// `s[..=0]` desugars to `s.subsequence(0, 0 + 1)` = `s.subsequence(0, 1)`.
/// Part of #2463.
#[test]
#[timeout(30000)]
fn test_cc_seq_g_inclusive_range_to_len_pipeline() {
    let req = ge(method_call(var("s"), "len", vec![]), int(1));
    let subseq = method_call(var("s"), "subsequence", vec![int(0), add(int(0), int(1))]);
    let ens = eq(method_call(subseq, "len", vec![]), int(1));

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "s[..=0].len() == 1 should verify, got {result:?}"
    );
}
