// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Driver-local MIR extraction diagnostics.
//!
//! These diagnostics explain why the MIR extractor returned `None` without
//! moving rustc-specific payloads into `trust-wp-core`. They are collected at
//! the `trust-wp-driver` boundary and surfaced selectively by callers.

use std::{cell::RefCell, fmt};

use rustc_middle::mir::Location;

use super::effects::CallEffects;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExtractionDiagKind {
    UnsupportedStatement,
    UnsupportedTerminator,
    ControlFlowCycle,
    UnsupportedSwitchShape,
    CallResolutionBacktrackFailed,
    UnevaluatedConstRecursionLimit,
    FeatureGap,
}

impl fmt::Display for ExtractionDiagKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::UnsupportedStatement => "unsupported statement",
            Self::UnsupportedTerminator => "unsupported terminator",
            Self::ControlFlowCycle => "control-flow cycle",
            Self::UnsupportedSwitchShape => "unsupported switch shape",
            Self::CallResolutionBacktrackFailed => "call resolution backtrack failed",
            Self::UnevaluatedConstRecursionLimit => "unevaluated const recursion limit",
            Self::FeatureGap => "feature gap",
        };
        f.write_str(label)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExtractionDiag {
    pub(crate) module: &'static str,
    pub(crate) kind: ExtractionDiagKind,
    pub(crate) detail: String,
    pub(crate) location: Option<Location>,
}

impl ExtractionDiag {
    #[must_use]
    pub(crate) fn render(&self) -> String {
        let location = self
            .location
            .map(|location| format!(" at {location:?}"))
            .unwrap_or_default();
        format!(
            "{}{} in {}: {}",
            self.kind, location, self.module, self.detail
        )
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ExtractionDiagnostics {
    pub(crate) entries: Vec<ExtractionDiag>,
}

impl ExtractionDiagnostics {
    pub(crate) fn record(
        &mut self,
        module: &'static str,
        kind: ExtractionDiagKind,
        detail: impl Into<String>,
        location: Option<Location>,
    ) {
        self.entries.push(ExtractionDiag {
            module,
            kind,
            detail: detail.into(),
            location,
        });
    }

    #[must_use]
    pub(crate) fn first(&self) -> Option<&ExtractionDiag> {
        self.entries.first()
    }

    #[must_use]
    pub(crate) fn render_summary(&self) -> Option<String> {
        let first = self.first()?;
        let remaining = self.entries.len() - 1;
        if remaining == 0 {
            Some(first.render())
        } else {
            Some(format!("{} (+{remaining} more)", first.render()))
        }
    }
}

pub(crate) type ExtractionDiagnosticSink = RefCell<ExtractionDiagnostics>;

#[derive(Debug)]
pub(crate) struct ExtractionOutcome<T> {
    pub(crate) value: Option<T>,
    pub(crate) effects: CallEffects,
    pub(crate) diagnostics: ExtractionDiagnostics,
}

pub(crate) fn record_extraction_diag(
    sink: Option<&ExtractionDiagnosticSink>,
    module: &'static str,
    kind: ExtractionDiagKind,
    detail: impl Into<String>,
    location: Option<Location>,
) {
    let Some(sink) = sink else {
        return;
    };
    sink.borrow_mut().record(module, kind, detail, location);
}
