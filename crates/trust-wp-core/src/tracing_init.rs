// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared tracing initialization for trust-wp binaries.
//!
//! Both `cargo-trust-wp` and `trust-wp-rustc` need identical tracing setup.
//! This module provides a single source of truth behind the `tracing-init`
//! feature flag.
//!
//! # Environment Variables
//!
//! - `TRUST_WP_LOG`: Custom tracing filter with stable aliases such as
//!   `"encoder=debug,verify=trace"` or raw directives like
//!   `"trust_wp_ay::verify=trace"`. When absent or invalid, tracing falls back
//!   to `warn` or the scoped verbose baseline.
//! - `TRUST_WP_DEBUG`: If set, appends `trust_wp_ay=debug` unless the filter
//!   already enables equivalent ay or global debug/trace logging.

#[path = "tracing_timing.rs"]
mod timing_layer;

use timing_layer::{TimingLayer, TimingVerbosity};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub const TIMING_STAGE_PARSE_SPAN: &str = timing_layer::STAGE_PARSE_SPAN;
pub const TIMING_STAGE_EXTRACT_SPAN: &str = timing_layer::STAGE_EXTRACT_SPAN;
pub const TIMING_STAGE_VC_SPAN: &str = timing_layer::STAGE_VC_SPAN;
pub const TIMING_STAGE_SOLVE_SPAN: &str = timing_layer::STAGE_SOLVE_SPAN;

const QUIET_FILTER_BASELINE: &str = "warn";
const VERBOSE_FILTER_BASELINE: &str =
    "warn,cargo_trust_wp=info,trust_wp_core=info,trust_wp_driver=info,trust_wp_ay=info";
const TRUST_WP_AY_DEBUG_DIRECTIVE: &str = "trust_wp_ay=debug";
const LOG_TARGET_ALIASES: [(&str, &str); 5] = [
    ("callbacks", "trust_wp_driver::callbacks"),
    ("mir_analysis", "trust_wp_driver::mir_analysis"),
    ("encoder", "trust_wp_ay::encoder"),
    ("verify", "trust_wp_ay::verify"),
    ("memory_model", "trust_wp_ay::memory_model"),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GlobalLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Off,
}

impl GlobalLevel {
    fn parse(directive: &str) -> Option<Self> {
        match directive {
            "trace" => Some(Self::Trace),
            "debug" => Some(Self::Debug),
            "info" => Some(Self::Info),
            "warn" => Some(Self::Warn),
            "error" => Some(Self::Error),
            "off" => Some(Self::Off),
            _ => None,
        }
    }

    fn is_debug_or_trace(self) -> bool {
        matches!(self, Self::Trace | Self::Debug)
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct NormalizedLogDirectives {
    directives: Vec<String>,
    global_level: Option<GlobalLevel>,
    targets_trust_wp_ay: bool,
}

pub fn trust_wp_log_help() -> String {
    let targets = LOG_TARGET_ALIASES
        .iter()
        .map(|(alias, _)| *alias)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "LOGGING:\n    TRUST_WP_LOG=<target>=<level>[,...]\n        targets: {targets}\n        example: TRUST_WP_LOG=callbacks=debug,verify=trace cargo trust-wp -v"
    )
}

fn default_filter_baseline(verbose: bool) -> &'static str {
    if verbose {
        VERBOSE_FILTER_BASELINE
    } else {
        QUIET_FILTER_BASELINE
    }
}

fn fallback_filter_string(verbose: bool, trust_wp_debug: bool) -> String {
    let mut directives = vec![default_filter_baseline(verbose).to_string()];
    if trust_wp_debug {
        directives.push(TRUST_WP_AY_DEBUG_DIRECTIVE.to_string());
    }
    directives.join(",")
}

fn build_filter_string(verbose: bool, trust_wp_log: Option<&str>, trust_wp_debug: bool) -> String {
    let Some(raw_filter) = trust_wp_log else {
        return fallback_filter_string(verbose, trust_wp_debug);
    };

    let normalized = normalize_trust_wp_log(raw_filter);
    let mut directives = Vec::with_capacity(normalized.directives.len() + 2);
    let append_trust_wp_ay_debug = trust_wp_debug && should_append_trust_wp_ay_debug(&normalized);

    if normalized.global_level.is_none() {
        directives.push(QUIET_FILTER_BASELINE.to_string());
    }

    directives.extend(normalized.directives);

    if append_trust_wp_ay_debug {
        directives.push(TRUST_WP_AY_DEBUG_DIRECTIVE.to_string());
    }

    directives.join(",")
}

fn build_env_filter(verbose: bool, trust_wp_log: Option<&str>, trust_wp_debug: bool) -> EnvFilter {
    let filter = build_filter_string(verbose, trust_wp_log, trust_wp_debug);
    let fallback_filter = fallback_filter_string(verbose, trust_wp_debug);
    EnvFilter::try_new(&filter).unwrap_or_else(|_| EnvFilter::new(fallback_filter))
}

fn normalize_trust_wp_log(raw_filter: &str) -> NormalizedLogDirectives {
    let mut normalized = NormalizedLogDirectives::default();

    for directive in raw_filter.split(',') {
        let directive = directive.trim();
        if directive.is_empty() {
            continue;
        }

        let (directive, global_level, targets_trust_wp_ay) = normalize_log_directive(directive);
        normalized.directives.push(directive);
        normalized.global_level = global_level.or(normalized.global_level);
        normalized.targets_trust_wp_ay |= targets_trust_wp_ay;
    }

    normalized
}

fn normalize_log_directive(directive: &str) -> (String, Option<GlobalLevel>, bool) {
    if let Some(level) = GlobalLevel::parse(directive) {
        return (directive.to_string(), Some(level), false);
    }

    if let Some((target, level)) = directive.split_once('=') {
        let target = expand_log_target_alias(target.trim());
        let normalized = format!("{target}={}", level.trim());
        return (
            normalized,
            None,
            target == "trust_wp_ay" || target.starts_with("trust_wp_ay::"),
        );
    }

    if directive.contains("::") {
        return (
            directive.to_string(),
            None,
            directive == "trust_wp_ay" || directive.starts_with("trust_wp_ay::"),
        );
    }

    (directive.to_string(), None, directive == "trust_wp_ay")
}

fn expand_log_target_alias(target: &str) -> &str {
    LOG_TARGET_ALIASES
        .iter()
        .find_map(|(alias, expanded)| (*alias == target).then_some(*expanded))
        .unwrap_or(target)
}

fn should_append_trust_wp_ay_debug(normalized: &NormalizedLogDirectives) -> bool {
    if normalized.targets_trust_wp_ay {
        return false;
    }
    !normalized
        .global_level
        .is_some_and(GlobalLevel::is_debug_or_trace)
}

/// Initialize trust-wp tracing with the standard env-var convention.
///
/// When `verbose` is true, the fallback filter raises trust-wp-owned targets to
/// `info`; otherwise the fallback is `warn`.
/// `TRUST_WP_LOG` accepts stable aliases and raw `EnvFilter` directives.
/// `TRUST_WP_DEBUG` appends `trust_wp_ay=debug` unless an equivalent ay-targeted or
/// global debug/trace directive is already present.
pub fn init_trust_wp_tracing(verbose: bool) {
    let trust_wp_log = std::env::var("TRUST_WP_LOG").ok();
    let trust_wp_debug = std::env::var_os("TRUST_WP_DEBUG").is_some();
    let env_filter = build_env_filter(verbose, trust_wp_log.as_deref(), trust_wp_debug);
    let timing_verbosity = TimingVerbosity::from_max_level(env_filter.max_level_hint());

    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_writer(std::io::stderr)
        .with_target(false)
        .with_level(false)
        .without_time()
        .with_ansi(false);

    let _ = tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .with(TimingLayer::new(timing_verbosity))
        .try_init();
}

#[cfg(test)]
mod tests {
    use tracing::level_filters::LevelFilter;

    use super::*;

    #[test]
    fn test_build_filter_expands_aliases() {
        let filter = build_filter_string(false, Some("encoder=debug,verify=trace"), false);
        assert_eq!(
            filter,
            "warn,trust_wp_ay::encoder=debug,trust_wp_ay::verify=trace"
        );
    }

    #[test]
    fn test_build_filter_preserves_raw_directive() {
        let filter = build_filter_string(false, Some("trust_wp_ay::verify=trace"), false);
        assert_eq!(filter, "warn,trust_wp_ay::verify=trace");
    }

    #[test]
    fn test_trust_wp_debug_does_not_append_when_ay_alias_present() {
        let filter = build_filter_string(false, Some("memory_model=trace"), true);
        assert_eq!(filter, "warn,trust_wp_ay::memory_model=trace");
    }

    #[test]
    fn test_invalid_trust_wp_log_falls_back_to_scoped_baseline() {
        let filter = build_env_filter(true, Some("["), false);
        let fallback = EnvFilter::new(VERBOSE_FILTER_BASELINE);
        assert_eq!(filter.max_level_hint(), Some(LevelFilter::INFO));
        assert_eq!(filter.to_string(), fallback.to_string());
    }

    #[test]
    fn test_trust_wp_log_help_mentions_aliases() {
        let help = trust_wp_log_help();
        assert!(help.contains("TRUST_WP_LOG=<target>=<level>[,...]"));
        assert!(help.contains("callbacks"));
        assert!(help.contains("memory_model"));
    }
}
