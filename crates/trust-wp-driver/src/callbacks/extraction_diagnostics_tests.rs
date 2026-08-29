// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::proof_assert_extract::format_proof_assert_extraction_message;
use crate::mir_analysis::diagnostics::{ExtractionDiagKind, ExtractionDiagnostics};

#[test]
fn test_format_proof_assert_extraction_message_includes_summary() {
    let mut diagnostics = ExtractionDiagnostics::default();
    diagnostics.record(
        "extract/branching.rs",
        ExtractionDiagKind::UnsupportedSwitchShape,
        "bool SwitchInt collapsed to a single successor",
        None,
    );
    diagnostics.record(
        "translate/mod.rs",
        ExtractionDiagKind::FeatureGap,
        "missing local expression for _7",
        None,
    );

    let message = format_proof_assert_extraction_message("crate::demo::f", &diagnostics);

    assert!(
        message.contains("proof_assert in crate::demo::f"),
        "message should preserve the proof_assert context: {message}"
    );
    assert!(
        message.contains("unsupported switch shape"),
        "message should include the diagnostic kind: {message}"
    );
    assert!(
        message.contains("(+1 more)"),
        "message should summarize additional diagnostics: {message}"
    );
    assert!(
        message.contains("using preconditions only"),
        "message should preserve the fallback semantics: {message}"
    );
}
