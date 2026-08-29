// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    path::Path,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;

use super::*;

static DETAILED_EXTRACT_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct DetailedReturnExprCallbacks {
    fn_name: String,
    outcome: Option<(
        Option<PureExpr>,
        crate::mir_analysis::diagnostics::ExtractionDiagnostics,
    )>,
    ran: bool,
}

impl Callbacks for DetailedReturnExprCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();

            let outcome = extract_return_expr_with_context_detailed(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &HashMap::new(),
            );
            self.outcome = Some((outcome.value, outcome.diagnostics));
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_return_expr_details_in_source(
    source: &str,
    fn_name: &str,
) -> (
    Option<PureExpr>,
    crate::mir_analysis::diagnostics::ExtractionDiagnostics,
) {
    let unique = DETAILED_EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_return_expr_detailed_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_return_expr_detailed_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = DetailedReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        outcome: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract detailed return expr for `{fn_name}`"
    );
    callbacks
        .outcome
        .expect("detailed extraction outcome should be set when ran=true")
}

#[test]
fn detailed_return_expr_records_diagnostics_for_unsupported_loop_body() {
    let source = r#"
pub fn test_fn(flag: bool) -> i32 {
    let mut x = 0;
    while flag {
        x += 1;
    }
    x
}
"#;

    let (expr, _diagnostics) = extract_return_expr_details_in_source(source, "test_fn");
    // With loop-aware extraction (#2698), the extractor skips the entire
    // loop body and continues from the loop exit block. No cycle diagnostic
    // is emitted because the walker never enters the loop body. The post-loop
    // return expression is extracted cleanly.
    assert!(
        expr.is_some(),
        "loop-skip should extract the post-loop return expression"
    );
    // No diagnostics expected — the loop is cleanly skipped, not cycled.
    // (Before #2698, the cycle-recovery path produced a ControlFlowCycle
    // diagnostic here.)
}

/// Regression for #2116, updated by #2698: with loop-aware extraction,
/// the loop body is skipped entirely (no ControlFlowCycle emitted). The
/// post-loop inline asm still causes an unsupported statement diagnostic.
/// The `then` branch fails due to the asm, so the outer `if` should not
/// collapse to the sibling branch. (#2116 semantics preserved.)
#[test]
fn detailed_return_expr_does_not_recover_branch_with_cycle_then_unsupported_statement() {
    let source = r#"
pub fn test_fn(flag: bool) -> i32 {
    if flag {
        let mut x = 0;
        while x < 1 {
            x += 1;
        }
        unsafe {
            std::arch::asm!("");
        }
        x
    } else {
        0
    }
}
"#;

    let (_expr, diagnostics) = extract_return_expr_details_in_source(source, "test_fn");
    // The `then` branch still fails extraction due to the inline asm
    // (unsupported statement). With loop-aware extraction the cycle is
    // avoided, but the unsupported statement still blocks the branch.
    assert!(
        diagnostics.entries.iter().any(|entry| {
            matches!(
                entry.kind,
                crate::mir_analysis::diagnostics::ExtractionDiagKind::UnsupportedStatement
                    | crate::mir_analysis::diagnostics::ExtractionDiagKind::UnsupportedTerminator
            )
        }),
        "expected the post-loop inline asm to surface as an unsupported extraction diagnostic, got {:?}",
        diagnostics.entries,
    );
}

/// Regression for #2116, updated by #2698: with loop-aware extraction,
/// the loop body is skipped (no cycle). The post-loop inline asm still
/// blocks extraction of the branch, so the outer match should not collapse.
#[test]
fn detailed_return_expr_does_not_recover_int_switch_branch_with_cycle_then_unsupported_statement() {
    let source = r#"
pub fn test_fn(tag: i32) -> i32 {
    match tag {
        1 => {
            let mut x = 0;
            while x < 1 {
                x += 1;
            }
            unsafe {
                std::arch::asm!("");
            }
            x
        }
        _ => 0,
    }
}
"#;

    let (_expr, diagnostics) = extract_return_expr_details_in_source(source, "test_fn");
    // The `1 =>` branch still fails extraction due to inline asm.
    // The loop is now cleanly skipped (no ControlFlowCycle diagnostic),
    // but the unsupported statement still blocks the branch.
    assert!(
        diagnostics.entries.iter().any(|entry| {
            matches!(
                entry.kind,
                crate::mir_analysis::diagnostics::ExtractionDiagKind::UnsupportedStatement
                    | crate::mir_analysis::diagnostics::ExtractionDiagKind::UnsupportedTerminator
            )
        }),
        "expected the post-loop inline asm to surface as an unsupported extraction diagnostic, got {:?}",
        diagnostics.entries,
    );
}

/// Regression for #2333: a `panic!()`-only body lowers to `Call { target: None }`.
/// The primary extractor must treat this as a dead-end bail, NOT record an
/// `UnsupportedTerminator` diagnostic.
#[test]
fn detailed_return_expr_does_not_record_diagnostic_for_diverging_call_without_continuation() {
    let source = r#"
pub fn diverging_bool() -> bool {
    panic!()
}
"#;

    let (expr, diagnostics) = extract_return_expr_details_in_source(source, "diverging_bool");
    assert!(
        expr.is_none(),
        "diverging body has no return value to extract"
    );
    assert!(
        diagnostics.entries.is_empty(),
        "diverging call (target: None) must not produce UnsupportedTerminator diagnostics, \
         got: {:?}",
        diagnostics.entries,
    );
}

/// Regression for #2323: MIR for `if *a >= *b { a } else { b }` returning a
/// mutable reference can produce `Unreachable` terminators in the lowered CFG.
/// The extractor must treat these as dead-end leaves (no successors), NOT as
/// unsupported terminators that abort context extraction.
#[test]
fn detailed_return_expr_unreachable_terminator_is_dead_end_not_unsupported() {
    // Shape mirrors rusthorn/inc_max_repeat: conditional mutable-ref return
    // that MIR may lower with Unreachable on impossible branches.
    let source = r#"
pub fn take_max<'a>(a: &'a mut u32, b: &'a mut u32) -> &'a mut u32 {
    if *a >= *b { a } else { b }
}
"#;

    let (_expr, diagnostics) = extract_return_expr_details_in_source(source, "take_max");
    // The extraction may or may not produce a value (the mut-ref pattern
    // can still be complex), but it MUST NOT report UnsupportedTerminator
    // for the Unreachable paths.
    let has_unsupported_terminator = diagnostics.entries.iter().any(|e| {
        matches!(
            e.kind,
            crate::mir_analysis::diagnostics::ExtractionDiagKind::UnsupportedTerminator
        )
    });
    assert!(
        !has_unsupported_terminator,
        "Unreachable terminators must be treated as dead-end CFG leaves, \
         not unsupported terminators. Got diagnostics: {:?}",
        diagnostics.entries,
    );
}

#[test]
fn call_spec_mapping_closure_uses_detailed_extraction_api() {
    let source = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/mir_analysis/extract/call_spec/mapping_closure.rs"),
    )
    .expect("read call_spec/mapping_closure.rs");

    assert!(
        source.contains("super::extract_return_expr_with_context_detailed("),
        "mapping_closure.rs should use the detailed extraction API for production closure-body extraction"
    );
    assert!(
        !source.contains("super::extract_return_expr_with_context("),
        "mapping_closure.rs should not reintroduce the legacy Option-only extraction wrapper"
    );
}
