// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared fixtures for trigger synthesis audit tests.

use crate::{
    encoder::{AYEncoder, SynthesizedTriggerDiagnostic},
    PureExpr,
};

pub(super) fn synthesized_trigger(
    vars: &[&str],
    patterns: Vec<Vec<PureExpr>>,
) -> SynthesizedTriggerDiagnostic {
    SynthesizedTriggerDiagnostic {
        vars: vars.iter().map(|var| (*var).to_string()).collect(),
        patterns,
    }
}

pub(super) fn assert_synthesized_triggers(
    encoder: &AYEncoder,
    expected: &[SynthesizedTriggerDiagnostic],
) {
    let mut actual = Vec::new();
    for diag in encoder.synthesized_triggers() {
        if !actual.contains(diag) {
            actual.push(diag.clone());
        }
    }
    assert_eq!(
        actual.len(),
        expected.len(),
        "unexpected synthesized trigger diagnostics: {actual:#?}"
    );
    for expected_diag in expected {
        assert!(
            actual.contains(expected_diag),
            "missing synthesized trigger diagnostic {expected_diag:#?} in {actual:#?}"
        );
    }
}
