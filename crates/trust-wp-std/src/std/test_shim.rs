// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared test-only helpers for parsing std spec strings.
//!
//! trust-wp-std cannot depend on trust-wp-driver (it would be circular), so
//! tests use this local parser shim that mirrors `StdSpec::from_spec_string`.

/// Minimal StdSpec for testing.
#[cfg(test)]
pub(super) struct StdSpec {
    pub(super) requires: Vec<String>,
    pub(super) ensures: Vec<String>,
}

/// Minimal spec string parser (mirrors `StdSpec::from_spec_string`).
#[cfg(test)]
pub(super) fn parse_spec_string(spec: &str) -> StdSpec {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut current_section: Option<&str> = None;
    let mut current_content = String::new();

    for line in spec.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        if trimmed.starts_with("requires:") {
            if let Some(section) = current_section {
                let content = current_content.trim().to_string();
                if !content.is_empty() {
                    if section == "requires" {
                        requires.push(content);
                    } else if section == "ensures" {
                        ensures.push(content);
                    }
                }
            }
            current_section = Some("requires");
            current_content = trimmed.trim_start_matches("requires:").trim().to_string();
        } else if trimmed.starts_with("ensures:") {
            if let Some(section) = current_section {
                let content = current_content.trim().to_string();
                if !content.is_empty() {
                    if section == "requires" {
                        requires.push(content);
                    } else if section == "ensures" {
                        ensures.push(content);
                    }
                }
            }
            current_section = Some("ensures");
            current_content = trimmed.trim_start_matches("ensures:").trim().to_string();
        } else if current_section.is_some() {
            if !current_content.is_empty() {
                current_content.push(' ');
            }
            current_content.push_str(trimmed);
        }
    }

    if let Some(section) = current_section {
        let content = current_content.trim().to_string();
        if !content.is_empty() {
            if section == "requires" {
                requires.push(content);
            } else if section == "ensures" {
                ensures.push(content);
            }
        }
    }

    StdSpec { requires, ensures }
}
