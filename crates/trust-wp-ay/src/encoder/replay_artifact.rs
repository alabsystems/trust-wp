// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Dependency-free replay artifact schema for AY solver replay capture.
//!
//! This module provides a compact, stable in-memory schema plus a recorder that
//! preserves solver-facing event order for trust-wp provenance.

#![allow(dead_code)]

pub(crate) const REPLAY_ARTIFACT_SCHEMA_VERSION: &str = "trust-wp-ay-replay-artifact-v1";

/// Complete replay artifact for one solver interaction trace.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReplayArtifact {
    pub schema_version: &'static str,
    pub name: String,
    pub events: Vec<ReplayEvent>,
}

impl ReplayArtifact {
    pub(crate) fn new(name: impl AsRef<str>) -> Self {
        Self {
            schema_version: REPLAY_ARTIFACT_SCHEMA_VERSION,
            name: sanitize_replay_name(name.as_ref()),
            events: Vec::new(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.events.len()
    }

    /// Render a deterministic text form suitable for snapshots or hashing.
    ///
    /// This is not a public wire format commitment; it exists so callers can
    /// materialize a replay artifact without pulling in serde.
    pub(crate) fn to_stable_text(&self) -> String {
        let mut text = String::new();
        text.push_str("schema=");
        text.push_str(self.schema_version);
        text.push('\n');
        text.push_str("name=");
        push_escaped(&mut text, &self.name);
        text.push('\n');
        text.push_str("events=");
        text.push_str(&self.events.len().to_string());
        text.push('\n');

        for event in &self.events {
            text.push_str("event.");
            text.push_str(&event.sequence.to_string());
            text.push('=');
            event.kind.push_stable_text(&mut text);
            text.push('\n');
        }

        text
    }
}

/// Builder/recorder that assigns monotonic sequence numbers to replay events.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReplayRecorder {
    artifact: ReplayArtifact,
    next_sequence: u64,
}

impl ReplayRecorder {
    pub(crate) fn new(name: impl AsRef<str>) -> Self {
        Self {
            artifact: ReplayArtifact::new(name),
            next_sequence: 0,
        }
    }

    pub(crate) fn artifact(&self) -> &ReplayArtifact {
        &self.artifact
    }

    pub(crate) fn into_artifact(self) -> ReplayArtifact {
        self.artifact
    }

    pub(crate) fn record_assert(
        &mut self,
        name: impl AsRef<str>,
        term: impl Into<String>,
    ) -> &ReplayEvent {
        self.record(ReplayEventKind::Assert {
            name: sanitize_replay_name(name.as_ref()),
            term: term.into(),
        })
    }

    pub(crate) fn record_push(&mut self, name: impl AsRef<str>) -> &ReplayEvent {
        self.record(ReplayEventKind::Push {
            name: sanitize_replay_name(name.as_ref()),
        })
    }

    pub(crate) fn record_pop(&mut self, frames: u32) -> &ReplayEvent {
        self.record(ReplayEventKind::Pop { frames })
    }

    pub(crate) fn record_check_sat(&mut self, name: impl AsRef<str>) -> &ReplayEvent {
        self.record(ReplayEventKind::CheckSat {
            name: sanitize_replay_name(name.as_ref()),
        })
    }

    pub(crate) fn record_result(&mut self, status: ReplayResultStatus) -> &ReplayEvent {
        self.record(ReplayEventKind::Result {
            status,
            detail: None,
        })
    }

    pub(crate) fn record_result_with_detail(
        &mut self,
        status: ReplayResultStatus,
        detail: impl Into<String>,
    ) -> &ReplayEvent {
        self.record(ReplayEventKind::Result {
            status,
            detail: Some(detail.into()),
        })
    }

    fn record(&mut self, kind: ReplayEventKind) -> &ReplayEvent {
        let sequence = self.next_sequence;
        self.next_sequence = self
            .next_sequence
            .checked_add(1)
            .expect("replay event sequence overflow");
        self.artifact.events.push(ReplayEvent { sequence, kind });
        self.artifact
            .events
            .last()
            .expect("just pushed replay event")
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReplayEvent {
    pub sequence: u64,
    pub kind: ReplayEventKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ReplayEventKind {
    Assert {
        name: String,
        term: String,
    },
    Push {
        name: String,
    },
    Pop {
        frames: u32,
    },
    CheckSat {
        name: String,
    },
    Result {
        status: ReplayResultStatus,
        detail: Option<String>,
    },
}

impl ReplayEventKind {
    fn push_stable_text(&self, text: &mut String) {
        match self {
            Self::Assert { name, term } => {
                text.push_str("assert|name=");
                push_escaped(text, name);
                text.push_str("|term=");
                push_escaped(text, term);
            }
            Self::Push { name } => {
                text.push_str("push|name=");
                push_escaped(text, name);
            }
            Self::Pop { frames } => {
                text.push_str("pop|frames=");
                text.push_str(&frames.to_string());
            }
            Self::CheckSat { name } => {
                text.push_str("check-sat|name=");
                push_escaped(text, name);
            }
            Self::Result { status, detail } => {
                text.push_str("result|status=");
                text.push_str(status.as_str());
                if let Some(detail) = detail {
                    text.push_str("|detail=");
                    push_escaped(text, detail);
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ReplayResultStatus {
    Sat,
    Unsat,
    Unknown,
}

impl ReplayResultStatus {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}

pub(crate) fn sanitize_replay_name(raw: &str) -> String {
    let mut sanitized = String::with_capacity(raw.len().max(1));
    let mut previous_was_separator = false;

    for ch in raw.chars() {
        let mapped = if ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '.') {
            ch
        } else {
            '_'
        };

        if mapped == '_' {
            if previous_was_separator {
                continue;
            }
            previous_was_separator = true;
        } else {
            previous_was_separator = false;
        }
        sanitized.push(mapped);
    }

    let sanitized = sanitized.trim_matches('_');
    if sanitized.is_empty() {
        return "event".to_string();
    }

    if sanitized
        .as_bytes()
        .first()
        .is_some_and(|byte| byte.is_ascii_digit())
    {
        format!("event_{sanitized}")
    } else {
        sanitized.to_string()
    }
}

fn push_escaped(out: &mut String, value: &str) {
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '|' => out.push_str("\\|"),
            '=' => out.push_str("\\="),
            ch => out.push(ch),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recorder_preserves_event_order() {
        let mut recorder = ReplayRecorder::new("vc main");

        recorder.record_assert("precondition", "(>= x 0)");
        recorder.record_push("branch 1");
        recorder.record_check_sat("obligation");
        recorder.record_result_with_detail(ReplayResultStatus::Unsat, "proved");
        recorder.record_pop(1);

        let artifact = recorder.into_artifact();
        let sequences: Vec<u64> = artifact.events.iter().map(|event| event.sequence).collect();

        assert_eq!(sequences, vec![0, 1, 2, 3, 4]);
        assert!(matches!(
            artifact.events[0].kind,
            ReplayEventKind::Assert { .. }
        ));
        assert!(matches!(
            artifact.events[1].kind,
            ReplayEventKind::Push { .. }
        ));
        assert!(matches!(
            artifact.events[2].kind,
            ReplayEventKind::CheckSat { .. }
        ));
        assert!(matches!(
            artifact.events[3].kind,
            ReplayEventKind::Result {
                status: ReplayResultStatus::Unsat,
                ..
            }
        ));
        assert!(matches!(
            artifact.events[4].kind,
            ReplayEventKind::Pop { .. }
        ));
    }

    #[test]
    fn recorder_sanitizes_artifact_and_event_names() {
        let mut recorder = ReplayRecorder::new("  module::f<T> obligation #1  ");

        recorder.record_assert("9:pre\ncondition!!", "true");
        recorder.record_push("branch/then");
        recorder.record_check_sat("check sat?");

        let artifact = recorder.into_artifact();

        assert_eq!(artifact.name, "module_f_T_obligation_1");
        assert_eq!(
            artifact.events[0].kind,
            ReplayEventKind::Assert {
                name: "event_9_pre_condition".to_string(),
                term: "true".to_string(),
            }
        );
        assert_eq!(
            artifact.events[1].kind,
            ReplayEventKind::Push {
                name: "branch_then".to_string(),
            }
        );
        assert_eq!(
            artifact.events[2].kind,
            ReplayEventKind::CheckSat {
                name: "check_sat".to_string(),
            }
        );
        assert_eq!(sanitize_replay_name("!!!"), "event");
    }

    #[test]
    fn stable_text_escapes_control_characters_without_serde() {
        let mut recorder = ReplayRecorder::new("vc");

        recorder.record_assert("a=b", "x|y\nz");
        recorder.record_result_with_detail(ReplayResultStatus::Unknown, "timeout\tlimit");

        let text = recorder.artifact().to_stable_text();

        assert!(text.contains("schema=trust-wp-ay-replay-artifact-v1\n"));
        assert!(text.contains("event.0=assert|name=a_b|term=x\\|y\\nz\n"));
        assert!(text.contains("event.1=result|status=unknown|detail=timeout\\tlimit\n"));
    }
}
