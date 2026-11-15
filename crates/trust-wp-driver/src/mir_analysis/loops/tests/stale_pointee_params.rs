// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! By-reference parameters a loop invalidates.

use std::{fs, sync::atomic::Ordering};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use super::{
    super::stale_pointee_params::{
        params_invalidated_by_loops, params_invalidated_by_loops_at_exits,
    },
    TEST_COUNTER,
};

/// Argument locals `params_invalidated_by_loops` reports for `fn_name`, asked
/// without a program point (every loop in the body counts).
fn invalidated_params(source: &str, fn_name: &str) -> Vec<usize> {
    invalidated_params_with(source, fn_name, false)
}

/// The same question asked at the ENSURES lane's program point: the loops from
/// which a `Return` of the body is reachable.
fn invalidated_params_at_exits(source: &str, fn_name: &str) -> Vec<usize> {
    invalidated_params_with(source, fn_name, true)
}

fn invalidated_params_with(source: &str, fn_name: &str, at_exits: bool) -> Vec<usize> {
    struct C {
        fn_name: String,
        at_exits: bool,
        out: Vec<usize>,
        ran: bool,
    }
    impl Callbacks for C {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let suffix = format!("::{}", self.fn_name);
            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                    continue;
                }
                let body = tcx.optimized_mir(local_def_id.to_def_id());
                let reported = if self.at_exits {
                    params_invalidated_by_loops_at_exits(body)
                } else {
                    params_invalidated_by_loops(body, None)
                };
                let mut out: Vec<usize> = reported.iter().map(|local| local.as_usize()).collect();
                out.sort_unstable();
                self.out = out;
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_stale_params_{}_{}",
        std::process::id(),
        unique
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");
    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_stale_params_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = C {
        fn_name: fn_name.to_string(),
        at_exits,
        out: Vec::new(),
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);
    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks.out
}

#[test]
fn a_loop_storing_through_a_mut_param_invalidates_it() {
    let out = invalidated_params(
        "pub fn f(a: &mut u32, n: u32) { let mut i = 0; while i < n { *a = 7; i += 1; } }",
        "f",
    );
    assert_eq!(out, vec![1], "`*a = 7` in the loop invalidates a: {out:?}");
}

#[test]
fn a_loop_passing_a_mut_param_to_a_call_invalidates_it() {
    let out = invalidated_params(
        "fn set(x: &mut u32) { *x = 7; }
         pub fn f(a: &mut u32, n: u32) { let mut i = 0; while i < n { set(a); i += 1; } }",
        "f",
    );
    assert_eq!(out, vec![1], "`set(a)` in the loop invalidates a: {out:?}");
}

#[test]
fn a_loop_that_only_reads_a_mut_param_leaves_it_alone() {
    let out = invalidated_params(
        "fn need(_x: u32) {}
         pub fn f(a: &mut u32, n: u32) { let mut i = 0; while i < n { need(*a); i += 1; } }",
        "f",
    );
    assert!(out.is_empty(), "a read is not a write site: {out:?}");
}

#[test]
fn a_write_outside_every_loop_does_not_invalidate_the_param() {
    let out = invalidated_params(
        "pub fn f(a: &mut u32, n: u32) { *a = 7; let mut i = 0; while i < n { i += 1; } }",
        "f",
    );
    assert!(
        out.is_empty(),
        "a pre-loop write is walked by the extraction, not this analysis: {out:?}"
    );
}

// The ENSURES lane's program point — the body's `Return` blocks.

#[test]
fn at_exits_a_loop_storing_through_a_mut_param_invalidates_it() {
    let out = invalidated_params_at_exits(
        "pub fn f(a: &mut u32, n: u32) -> u32 { let mut i = 0; while i < n { *a = 7; i += 1; } *a }",
        "f",
    );
    assert_eq!(
        out,
        vec![1],
        "a loop that writes `*a` on the way to the return invalidates a: {out:?}"
    );
}

#[test]
fn at_exits_a_write_outside_every_loop_does_not_invalidate_the_param() {
    let out = invalidated_params_at_exits(
        "pub fn f(a: &mut u32, n: u32) -> u32 { *a = 7; let mut i = 0; while i < n { i += 1; } *a }",
        "f",
    );
    assert!(
        out.is_empty(),
        "a pre-loop write is walked by the extraction, not this analysis: {out:?}"
    );
}

#[test]
fn at_exits_a_loop_no_return_is_reachable_from_contributes_nothing() {
    // The writing loop sits on a path that always diverges, so no exit is
    // reachable from it and no postcondition is ever checked after it. The
    // point-free query still reports the parameter; this one must not.
    let source = "pub fn f(a: &mut u32, n: u32, c: bool) -> u32 {
             if c {
                 let mut i = 0;
                 while i < n { *a = 7; i += 1; }
                 panic!()
             }
             *a
         }";
    assert_eq!(
        invalidated_params(source, "f"),
        vec![1],
        "the point-free query reports every loop's write"
    );
    let out = invalidated_params_at_exits(source, "f");
    assert!(
        out.is_empty(),
        "no return is reachable from the writing loop: {out:?}"
    );
}
