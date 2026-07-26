// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::BTreeMap,
    io::{self, Write},
    sync::Mutex,
    time::{Duration, Instant},
};

use tracing::{
    field::{Field, Visit},
    level_filters::LevelFilter,
    span::{Attributes, Id},
    Subscriber,
};
use tracing_subscriber::{
    layer::{Context, Layer},
    registry::LookupSpan,
};

pub(super) const VERIFY_CONTRACTS_SPAN: &str = "trust_wp::verify_contracts";
pub(super) const VERIFY_FUNCTION_SPAN: &str = "trust_wp::verify_function";
pub(super) const STAGE_PARSE_SPAN: &str = "trust_wp::parse";
pub(super) const STAGE_EXTRACT_SPAN: &str = "trust_wp::extract";
pub(super) const STAGE_VC_SPAN: &str = "trust_wp::vc_gen";
pub(super) const STAGE_SOLVE_SPAN: &str = "trust_wp::solve";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TimingVerbosity {
    Quiet,
    Info,
    Debug,
}

impl TimingVerbosity {
    pub(super) fn from_max_level(level: Option<LevelFilter>) -> Self {
        match level {
            Some(LevelFilter::TRACE | LevelFilter::DEBUG) => Self::Debug,
            Some(LevelFilter::INFO) => Self::Info,
            _ => Self::Quiet,
        }
    }

    fn includes_info(self) -> bool {
        matches!(self, Self::Info | Self::Debug)
    }

    fn includes_debug(self) -> bool {
        matches!(self, Self::Debug)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stage {
    Parse,
    Extract,
    VcGen,
    Solve,
}

impl Stage {
    fn label(self) -> &'static str {
        match self {
            Self::Parse => "parse",
            Self::Extract => "extract",
            Self::VcGen => "vc",
            Self::Solve => "solve",
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FunctionTiming {
    def_path: String,
    total: Duration,
    parse: Duration,
    extract: Duration,
    vc_gen: Duration,
    solve: Duration,
}

impl FunctionTiming {
    fn new(def_path: &str) -> Self {
        Self {
            def_path: def_path.to_string(),
            ..Self::default()
        }
    }

    fn add_stage(&mut self, stage: Stage, duration: Duration) {
        match stage {
            Stage::Parse => self.parse += duration,
            Stage::Extract => self.extract += duration,
            Stage::VcGen => self.vc_gen += duration,
            Stage::Solve => self.solve += duration,
        }
    }

    fn summary_line(&self) -> String {
        format!(
            "trust-wp timing: {}: {} (parse: {}, extract: {}, vc: {}, solve: {})",
            self.def_path,
            format_duration(self.total),
            format_duration(self.parse),
            format_duration(self.extract),
            format_duration(self.vc_gen),
            format_duration(self.solve),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RunTimingSummary {
    total: Duration,
    slowest: Option<(String, Duration)>,
    solve_total: Duration,
}

impl RunTimingSummary {
    fn summary_line(&self) -> String {
        let total_nanos = self.total.as_nanos();
        let solve_pct = (self.solve_total.as_nanos() * 100)
            .checked_div(total_nanos)
            .unwrap_or(0);
        match &self.slowest {
            Some((def_path, duration)) => format!(
                "trust-wp timing: total {}, slowest {} ({}), solve {}% ({})",
                format_duration(self.total),
                def_path,
                format_duration(*duration),
                solve_pct,
                format_duration(self.solve_total),
            ),
            None => format!(
                "trust-wp timing: total {}, solve {}% ({})",
                format_duration(self.total),
                solve_pct,
                format_duration(self.solve_total),
            ),
        }
    }
}

#[derive(Default)]
struct TimingState {
    run: Option<RunState>,
}

#[derive(Default)]
struct RunState {
    functions: BTreeMap<String, FunctionTiming>,
}

impl TimingState {
    fn start_run(&mut self) {
        self.run = Some(RunState::default());
    }

    fn record_stage(&mut self, def_path: &str, stage: Stage, duration: Duration) {
        let Some(run) = self.run.as_mut() else {
            return;
        };
        run.functions
            .entry(def_path.to_string())
            .or_insert_with(|| FunctionTiming::new(def_path))
            .add_stage(stage, duration);
    }

    fn finish_function(&mut self, def_path: &str, duration: Duration) -> Option<FunctionTiming> {
        let run = self.run.as_mut()?;
        let function = run
            .functions
            .entry(def_path.to_string())
            .or_insert_with(|| FunctionTiming::new(def_path));
        function.total = duration;
        Some(function.clone())
    }

    fn finish_run(&mut self, duration: Duration) -> Option<RunTimingSummary> {
        let run = self.run.take()?;
        let functions: Vec<FunctionTiming> = run
            .functions
            .into_values()
            .filter(|function| function.total > Duration::ZERO)
            .collect();
        if functions.is_empty() {
            return None;
        }
        let solve_total: Duration = functions.iter().map(|function| function.solve).sum();
        let slowest = functions
            .iter()
            .max_by_key(|function| function.total)
            .map(|function| (function.def_path.clone(), function.total));
        Some(RunTimingSummary {
            total: duration,
            slowest,
            solve_total,
        })
    }
}

#[derive(Clone, Debug)]
struct SpanTiming {
    started: Instant,
    kind: SpanKind,
    function_def_path: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SpanKind {
    VerifyContracts,
    VerifyFunction { def_path: String },
    Stage(Stage),
    Other,
}

impl SpanKind {
    fn from_name(name: &str, def_path: Option<String>) -> Self {
        match name {
            VERIFY_CONTRACTS_SPAN => Self::VerifyContracts,
            VERIFY_FUNCTION_SPAN => Self::VerifyFunction {
                def_path: def_path.unwrap_or_default(),
            },
            STAGE_PARSE_SPAN => Self::Stage(Stage::Parse),
            STAGE_EXTRACT_SPAN => Self::Stage(Stage::Extract),
            STAGE_VC_SPAN => Self::Stage(Stage::VcGen),
            STAGE_SOLVE_SPAN => Self::Stage(Stage::Solve),
            _ => Self::Other,
        }
    }
}

#[derive(Default)]
struct DefPathVisitor {
    def_path: Option<String>,
}

impl Visit for DefPathVisitor {
    fn record_str(&mut self, field: &Field, value: &str) {
        if field.name() == "def_path" {
            self.def_path = Some(value.to_string());
        }
    }

    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        if field.name() != "def_path" {
            return;
        }
        let rendered = format!("{value:?}");
        self.def_path = Some(rendered.trim_matches('"').to_string());
    }
}

pub(super) struct TimingLayer {
    verbosity: TimingVerbosity,
    state: Mutex<TimingState>,
}

impl TimingLayer {
    pub(super) fn new(verbosity: TimingVerbosity) -> Self {
        Self {
            verbosity,
            state: Mutex::new(TimingState::default()),
        }
    }

    fn print_line(line: &str) {
        let mut stderr = io::stderr().lock();
        let _ = writeln!(stderr, "{line}");
    }

    fn inherited_function_def_path<S>(
        attrs: &Attributes<'_>,
        ctx: &Context<'_, S>,
    ) -> Option<String>
    where
        S: Subscriber + for<'lookup> LookupSpan<'lookup>,
    {
        let parent = if let Some(parent) = attrs.parent() {
            ctx.span(parent)
        } else if attrs.is_contextual() {
            ctx.lookup_current()
        } else {
            None
        }?;

        let inherited = parent
            .extensions()
            .get::<SpanTiming>()
            .and_then(|timing| timing.function_def_path.clone());
        inherited
    }
}

impl<S> Layer<S> for TimingLayer
where
    S: Subscriber + for<'lookup> LookupSpan<'lookup>,
{
    fn on_new_span(&self, attrs: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let mut visitor = DefPathVisitor::default();
        attrs.record(&mut visitor);

        let kind = SpanKind::from_name(attrs.metadata().name(), visitor.def_path.clone());
        let function_def_path = match &kind {
            SpanKind::VerifyFunction { def_path } if !def_path.is_empty() => Some(def_path.clone()),
            _ => Self::inherited_function_def_path(attrs, &ctx),
        };

        if matches!(kind, SpanKind::VerifyContracts) {
            self.state
                .lock()
                .expect("timing state mutex poisoned")
                .start_run();
        }

        let Some(span) = ctx.span(id) else {
            return;
        };
        span.extensions_mut().insert(SpanTiming {
            started: Instant::now(),
            kind,
            function_def_path,
        });
    }

    fn on_close(&self, id: Id, ctx: Context<'_, S>) {
        let Some(span) = ctx.span(&id) else {
            return;
        };
        let Some(timing) = span.extensions().get::<SpanTiming>().cloned() else {
            return;
        };
        let elapsed = timing.started.elapsed();

        match timing.kind {
            SpanKind::Stage(stage) => {
                let Some(def_path) = timing.function_def_path.as_deref() else {
                    return;
                };
                self.state
                    .lock()
                    .expect("timing state mutex poisoned")
                    .record_stage(def_path, stage, elapsed);
                if self.verbosity.includes_debug() {
                    Self::print_line(&format!(
                        "trust-wp timing: {} {}: {}",
                        def_path,
                        stage.label(),
                        format_duration(elapsed),
                    ));
                }
            }
            SpanKind::VerifyFunction { def_path } => {
                let Some(function) = self
                    .state
                    .lock()
                    .expect("timing state mutex poisoned")
                    .finish_function(&def_path, elapsed)
                else {
                    return;
                };
                if self.verbosity.includes_info() {
                    Self::print_line(&function.summary_line());
                }
            }
            SpanKind::VerifyContracts => {
                let Some(summary) = self
                    .state
                    .lock()
                    .expect("timing state mutex poisoned")
                    .finish_run(elapsed)
                else {
                    return;
                };
                if self.verbosity.includes_info() {
                    Self::print_line(&summary.summary_line());
                }
            }
            SpanKind::Other => {}
        }
    }
}

fn format_duration(duration: Duration) -> String {
    if duration.is_zero() {
        "0ms".to_string()
    } else if duration >= Duration::from_secs(1) {
        format!("{:.1}s", duration.as_secs_f64())
    } else if duration >= Duration::from_millis(1) {
        format!("{}ms", duration.as_millis())
    } else if duration >= Duration::from_micros(1) {
        format!("{}us", duration.as_micros())
    } else {
        format!("{}ns", duration.as_nanos())
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use tracing::level_filters::LevelFilter;

    use super::{
        format_duration, FunctionTiming, RunTimingSummary, Stage, TimingState, TimingVerbosity,
    };

    #[test]
    fn timing_verbosity_tracks_max_level() {
        assert_eq!(
            TimingVerbosity::from_max_level(Some(LevelFilter::DEBUG)),
            TimingVerbosity::Debug
        );
        assert_eq!(
            TimingVerbosity::from_max_level(Some(LevelFilter::INFO)),
            TimingVerbosity::Info
        );
        assert_eq!(
            TimingVerbosity::from_max_level(Some(LevelFilter::WARN)),
            TimingVerbosity::Quiet
        );
    }

    #[test]
    fn format_duration_uses_human_scales() {
        assert_eq!(format_duration(Duration::from_nanos(500)), "500ns");
        assert_eq!(format_duration(Duration::from_micros(42)), "42us");
        assert_eq!(format_duration(Duration::from_millis(75)), "75ms");
        assert_eq!(format_duration(Duration::from_millis(1500)), "1.5s");
    }

    #[test]
    fn function_summary_formats_expected_line() {
        let mut function = FunctionTiming::new("crate::increment");
        function.total = Duration::from_millis(100);
        function.add_stage(Stage::Parse, Duration::from_millis(2));
        function.add_stage(Stage::Extract, Duration::from_millis(15));
        function.add_stage(Stage::VcGen, Duration::from_millis(8));
        function.add_stage(Stage::Solve, Duration::from_millis(75));
        assert_eq!(
            function.summary_line(),
            "trust-wp timing: crate::increment: 100ms (parse: 2ms, extract: 15ms, vc: 8ms, solve: 75ms)"
        );
    }

    #[test]
    fn run_summary_reports_slowest_and_solve_share() {
        let summary = RunTimingSummary {
            total: Duration::from_secs(2),
            slowest: Some(("crate::slow".to_string(), Duration::from_millis(1200))),
            solve_total: Duration::from_millis(1500),
        };
        assert_eq!(
            summary.summary_line(),
            "trust-wp timing: total 2.0s, slowest crate::slow (1.2s), solve 75% (1.5s)"
        );
    }

    #[test]
    fn timing_state_accumulates_stage_and_total_durations() {
        let mut state = TimingState::default();
        state.start_run();
        state.record_stage("crate::f", Stage::Parse, Duration::from_millis(3));
        state.record_stage("crate::f", Stage::Solve, Duration::from_millis(9));
        let function = state
            .finish_function("crate::f", Duration::from_millis(20))
            .expect("function timing should exist");
        assert_eq!(function.parse, Duration::from_millis(3));
        assert_eq!(function.solve, Duration::from_millis(9));
        assert_eq!(function.total, Duration::from_millis(20));

        let summary = state
            .finish_run(Duration::from_millis(20))
            .expect("run summary should exist");
        assert_eq!(summary.solve_total, Duration::from_millis(9));
        assert_eq!(
            summary.slowest,
            Some(("crate::f".to_string(), Duration::from_millis(20)))
        );
    }
}
