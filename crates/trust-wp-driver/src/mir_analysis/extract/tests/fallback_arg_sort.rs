// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{Local, Operand, Place};
use rustc_span::{Spanned, DUMMY_SP};
use trust_wp_core::formula::ExprSort;

use super::*;

static FALLBACK_ARG_SORT_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Test callback that captures translated fallback args for a synthetic operand
/// built from the target function's first argument local.
struct FallbackArgSortCallbacks {
    fn_name: String,
    translated_args: Option<Vec<TranslatedArg>>,
    ran: bool,
}

impl Callbacks for FallbackArgSortCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let fn_suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&fn_suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_local = body
                .args_iter()
                .next()
                .expect("test_fn should have an argument local");
            let local_exprs: HashMap<Local, PureExpr> = HashMap::new();
            let synthetic_args = [Spanned {
                node: Operand::Move(Place::from(arg_local)),
                span: DUMMY_SP,
            }];

            let translated = translate_call_args_for_substitutions_with_tcx(
                &synthetic_args,
                &local_exprs,
                Some(body),
                Some(tcx),
            );
            self.translated_args = Some(translated);
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn translate_fallback_args_in_source(source: &str, fn_name: &str) -> Vec<TranslatedArg> {
    let unique = FALLBACK_ARG_SORT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_fallback_arg_sort_{}_{}",
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
        "trust_wp_fallback_arg_sort_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = FallbackArgSortCallbacks {
        fn_name: fn_name.to_string(),
        translated_args: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to find `{fn_name}` in compiled source"
    );
    callbacks
        .translated_args
        .expect("translated_args should be set when ran=true")
}

#[test]
fn translate_call_args_fallback_preserves_option_sort_from_mir() {
    let source = r#"
pub fn test_fn(x: Option<i32>) -> i32 {
    if x.is_some() { 1 } else { 0 }
}
"#;

    let translated = translate_fallback_args_in_source(source, "test_fn");
    let fallback = translated
        .iter()
        .find(|arg| arg.is_fallback)
        .expect("expected synthetic Option<T> operand to translate as a fallback arg");

    assert!(
        matches!(
            &fallback.expr,
            PureExpr::Var(name, Some(ExprSort::Datatype(_)))
                if name.starts_with("$fallback_arg0_")
        ),
        "fallback arg should preserve Option<T>'s MIR datatype sort, got {:?}",
        fallback.expr
    );
}
