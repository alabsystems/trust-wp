// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared test assertion helpers for std_specs tests.

use super::super::*;

pub(super) fn assert_ensures_contains(spec: &StdSpec, needle: &str, context: &str) {
    assert!(
        spec.ensures.iter().any(|e| e.contains(needle)),
        "{context} ensures must contain `{needle}`: {:?}",
        spec.ensures
    );
}

pub(super) fn assert_requires_contains(spec: &StdSpec, needle: &str, context: &str) {
    assert!(
        spec.requires.iter().any(|r| r.contains(needle)),
        "{context} requires must contain `{needle}`: {:?}",
        spec.requires
    );
}

pub(super) fn assert_param_names(spec: &StdSpec, expected: &[&str], context: &str) {
    let expected_vec: Vec<String> = expected.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(
        spec.param_names.as_deref(),
        Some(expected_vec.as_slice()),
        "{context} param_names mismatch"
    );
}
