// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Counterexample reporting for verification failures.

use trust_wp_ay::{CounterexampleType, SourceSpan, VarOrigin};

/// Names the encoder mints for itself, which mean nothing to the reader.
///
/// A counterexample is the tool's most important output: the reader is being
/// handed the inputs that break their contract. Every line that is not one of
/// those inputs makes that harder to see. `__trust_wp_ite_int_aux_0 = -1` names
/// a branch temporary the WP transform created; the heap/domain/perms trio
/// belongs to the memory model.
fn is_internal_var(name: &str) -> bool {
    // Matched precisely, not by bare prefix: the memory model's names are
    // `heap`, `domain`, `perms` and their `heap_contents`-style derivatives,
    // and a user is entitled to a variable called `heapsort_pivot` or
    // `domainname` without it being deleted from the report.
    const MEMORY_MODEL: [&str; 3] = ["heap", "domain", "perms"];
    MEMORY_MODEL.iter().any(|internal| {
        name == *internal
            || name
                .strip_prefix(internal)
                .is_some_and(|rest| rest.starts_with('_'))
    }) || name.starts_with("__trust_wp")
        || name.contains(trust_wp_core::formula::SYNTHESIZED_NAME_SIGIL)
}

/// Drop `x_view` when `x` is present with the same value.
///
/// `x@` — the mathematical view of `x` — is the identity for scalars, so the
/// model binds both and prints the same number twice under two names, one of
/// which the user never wrote. When the two disagree (a collection, a wrapping
/// carrier) the view is real information and is kept.
fn shadows_its_base<'a>(
    value: &trust_wp_ay::CounterexampleValue,
    all: &'a [&'a trust_wp_ay::CounterexampleValue],
) -> bool {
    let Some(base) = value.name.strip_suffix("_view") else {
        return false;
    };
    // Only an encoder-minted binding may be dropped. `fn f(row: i32, row_view:
    // i32)` is a legal signature, and a model that happens to give both the
    // same number must still report both — the reader wrote `row_view` and is
    // owed its value. A view the encoder synthesised carries no source origin.
    if !matches!(value.origin, None | Some(trust_wp_ay::VarOrigin::Internal)) {
        return false;
    }
    let rendered = format_counterexample_value(&value.value);
    all.iter()
        .any(|other| other.name == base && format_counterexample_value(&other.value) == rendered)
}

/// Report a counterexample from verification failure.
pub(super) fn report_counterexample(ce: &trust_wp_ay::Counterexample) {
    let named: Vec<_> = ce
        .values
        .iter()
        .filter(|val| !is_internal_var(&val.name))
        .collect();

    let filtered_values: Vec<_> = named
        .iter()
        .copied()
        .filter(|val| !shadows_its_base(val, &named))
        .collect();

    if !filtered_values.is_empty() {
        eprintln!("  counterexample:");
        for val in filtered_values {
            let origin_str = format_var_origin(val.origin.as_ref());
            let value_str = format_counterexample_value(&val.value);
            if origin_str.is_empty() {
                eprintln!("    {} = {}", val.name, value_str);
            } else {
                eprintln!("    {} = {} {}", val.name, value_str, origin_str);
            }
        }
    }
}

fn format_counterexample_value(value: &CounterexampleType) -> String {
    match value {
        // `ModelValue`'s own Display is SMT-LIB, which spells a negative
        // integer `(- 1)`. This line is read next to the user's Rust source,
        // where that number is written `-1`.
        CounterexampleType::Int(int) => int.to_string(),
        CounterexampleType::Seq(elements) => {
            let rendered = elements
                .iter()
                .map(format_counterexample_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{rendered}]")
        }
        CounterexampleType::Datatype { constructor, args } => {
            if args.is_empty() {
                constructor.clone()
            } else {
                let rendered = args
                    .iter()
                    .map(format_counterexample_value)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{constructor}({rendered})")
            }
        }
        CounterexampleType::Array { default, stores } => {
            let rendered_stores = stores
                .iter()
                .map(|(idx, value)| {
                    format!(
                        "{} -> {}",
                        format_counterexample_value(idx),
                        format_counterexample_value(value)
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "default {}; [{}]",
                format_counterexample_value(default),
                rendered_stores
            )
        }
        CounterexampleType::ArraySmtlib(smtlib) => smtlib.clone(),
        CounterexampleType::Unknown => "unknown".to_string(),
        _ => value.to_string(),
    }
}

/// Format a variable origin as a human-readable string.
///
/// When the origin carries a `SourceSpan` with file+line+column, the span
/// is appended in the form ` at file:line:col` so users can jump to the
/// parameter / clause that produced the counterexample binding (Phase 8a).
pub(super) fn format_var_origin(origin: Option<&VarOrigin>) -> String {
    let (base, span) = match origin {
        Some(VarOrigin::Parameter { name, span }) => (format!("(parameter {name})"), span.as_ref()),
        Some(VarOrigin::Precondition { contract_idx, span }) => {
            (format!("(from requires #{contract_idx})"), span.as_ref())
        }
        Some(VarOrigin::Postcondition { contract_idx, span }) => {
            (format!("(from ensures #{contract_idx})"), span.as_ref())
        }
        Some(VarOrigin::Invariant { span }) => ("(from invariant)".to_string(), span.as_ref()),
        Some(VarOrigin::MirLocal { local, span }) => (format!("(_{local} local)"), span.as_ref()),
        Some(VarOrigin::ReturnValue) => ("(return value)".to_string(), None),
        Some(VarOrigin::Internal) | None => (String::new(), None),
        Some(_) => ("(unknown origin)".to_string(), None),
    };
    if base.is_empty() {
        return base;
    }
    match span.and_then(format_source_span) {
        Some(suffix) => format!("{base} at {suffix}"),
        None => base,
    }
}

/// Render a `SourceSpan` as `file:line:col` when complete enough to be
/// actionable. Returns `None` for spans missing location data (synthetic
/// or contract-only spans) so the caller can omit the suffix.
fn format_source_span(span: &SourceSpan) -> Option<String> {
    let file = span.file.as_ref()?;
    let line = span.line?;
    let column = span.column?;
    Some(format!("{file}:{line}:{column}"))
}

#[cfg(test)]
mod tests {
    use trust_wp_ay::{CounterexampleType, CounterexampleValue, SourceSpan, VarOrigin};

    use super::{
        format_counterexample_value, format_var_origin, is_internal_var, shadows_its_base,
    };

    fn value(name: &str, int: i64) -> CounterexampleValue {
        CounterexampleValue {
            name: name.to_string(),
            value: CounterexampleType::Int(int.into()),
            origin: None,
        }
    }

    fn parameter(name: &str, int: i64) -> CounterexampleValue {
        CounterexampleValue {
            name: name.to_string(),
            value: CounterexampleType::Int(int.into()),
            origin: Some(VarOrigin::Parameter {
                name: name.to_string(),
                span: None,
            }),
        }
    }

    /// The reader asked which inputs break their contract. Encoder temporaries
    /// and memory-model bookkeeping are not inputs.
    #[test]
    fn encoder_internal_bindings_are_not_shown() {
        assert!(is_internal_var("__trust_wp_ite_int_aux_0"));
        assert!(is_internal_var("heap_contents"));
        assert!(is_internal_var("domain_0"));
        assert!(is_internal_var("perms_0"));
        assert!(!is_internal_var("x"));
        assert!(!is_internal_var("result"));
        // A user variable may legitimately start with these words.
        assert!(!is_internal_var("heapsort_pivot"));
        assert!(!is_internal_var("domainname"));
        assert!(!is_internal_var("permsission"));
        // ...while the memory model's own derivatives stay hidden.
        assert!(is_internal_var("heap_contents"));
        assert!(is_internal_var("domain_0"));
    }

    #[test]
    fn a_scalar_view_that_repeats_its_base_is_dropped() {
        let x = value("x", 1);
        let x_view = value("x_view", 1);
        let all = vec![&x, &x_view];
        assert!(shadows_its_base(&x_view, &all));
        // The base itself is always kept.
        assert!(!shadows_its_base(&x, &all));
    }

    #[test]
    fn a_view_that_differs_from_its_base_is_information_and_stays() {
        let v = value("v", 7);
        let v_view = value("v_view", 3);
        let all = vec![&v, &v_view];
        assert!(!shadows_its_base(&v_view, &all));
        // ...and so is a view with no base binding at all.
        let lone = value("w_view", 3);
        let only = vec![&lone];
        assert!(!shadows_its_base(&lone, &only));
    }

    /// `fn f(row: i32, row_view: i32)` is a legal signature. The reader wrote
    /// `row_view`; a coincidence of values must not delete it from the report.
    #[test]
    fn a_users_own_binding_named_view_is_never_dropped() {
        let row = parameter("row", 7);
        let row_view = parameter("row_view", 7);
        let all = vec![&row, &row_view];
        assert!(!shadows_its_base(&row_view, &all));
    }

    #[test]
    fn format_var_origin_parameter_with_full_span_includes_location() {
        let origin = VarOrigin::Parameter {
            name: "x".to_string(),
            span: Some(SourceSpan {
                file: Some("src/main.rs".to_string()),
                start: 0,
                end: 1,
                line: Some(12),
                column: Some(8),
            }),
        };
        assert_eq!(
            format_var_origin(Some(&origin)),
            "(parameter x) at src/main.rs:12:8"
        );
    }

    #[test]
    fn format_var_origin_parameter_without_span_omits_location_suffix() {
        let origin = VarOrigin::Parameter {
            name: "x".to_string(),
            span: None,
        };
        assert_eq!(format_var_origin(Some(&origin)), "(parameter x)");
    }

    #[test]
    fn format_var_origin_contract_only_span_omits_location_suffix() {
        // `SourceSpan::from_contract` produces a span with byte offsets but
        // no file/line/column. The diagnostic should omit the `at ...` suffix
        // rather than emit a half-formed location like `at :0:0`.
        let origin = VarOrigin::Precondition {
            contract_idx: 0,
            span: Some(SourceSpan::from_contract(2, 9)),
        };
        assert_eq!(format_var_origin(Some(&origin)), "(from requires #0)");
    }

    #[test]
    fn format_var_origin_return_value_has_no_span_field() {
        // `ReturnValue` carries no span; ensure no spurious `at ...` suffix.
        assert_eq!(
            format_var_origin(Some(&VarOrigin::ReturnValue)),
            "(return value)"
        );
    }

    #[test]
    fn negative_integers_are_rendered_the_way_rust_writes_them() {
        assert_eq!(
            format_counterexample_value(&CounterexampleType::Int((-1).into())),
            "-1"
        );
        assert_eq!(
            format_counterexample_value(&CounterexampleType::Int(42.into())),
            "42"
        );
    }

    #[test]
    fn format_counterexample_sequence_as_concrete_list() {
        let value = CounterexampleType::Seq(vec![
            CounterexampleType::Int(1.into()),
            CounterexampleType::Int(2.into()),
            CounterexampleType::Int(3.into()),
        ]);

        assert_eq!(format_counterexample_value(&value), "[1, 2, 3]");
    }

    #[test]
    fn format_counterexample_datatype_as_constructor_call() {
        let value = CounterexampleType::Datatype {
            constructor: "Some".to_string(),
            args: vec![CounterexampleType::Int(1.into())],
        };

        assert_eq!(format_counterexample_value(&value), "Some(1)");
    }

    #[test]
    fn format_counterexample_array_includes_default_and_updates() {
        let value = CounterexampleType::Array {
            default: Box::new(CounterexampleType::Int(0.into())),
            stores: vec![
                (
                    CounterexampleType::Int(1.into()),
                    CounterexampleType::Int(42.into()),
                ),
                (
                    CounterexampleType::Int(4.into()),
                    CounterexampleType::Int(7.into()),
                ),
            ],
        };

        assert_eq!(
            format_counterexample_value(&value),
            "default 0; [1 -> 42, 4 -> 7]"
        );
    }

    #[test]
    fn format_counterexample_bitvec_uses_solver_hex_display() {
        let value = CounterexampleType::BitVec {
            value: 0x2a.into(),
            width: 8,
        };

        assert_eq!(format_counterexample_value(&value), "#x2a");
    }
}
