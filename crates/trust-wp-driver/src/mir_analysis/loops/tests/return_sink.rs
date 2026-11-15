// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The return sink a loop function's rebuilt obligations carry.

use std::{collections::HashSet, fs, sync::atomic::Ordering};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use super::{super::detect_loops, TEST_COUNTER};
use crate::mir_analysis::body_returns_a_stale_store_read;

/// `body_returns_a_stale_store_read` for `fn_name`, with every loop body's
/// stores left to the loop lane (`loop_lane`) or counted (the loop-free sink).
fn trips_the_sink(source: &str, fn_name: &str, loop_lane: bool) -> bool {
    struct C {
        fn_name: String,
        loop_lane: bool,
        out: Option<bool>,
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
                let loop_blocks: HashSet<_> = if self.loop_lane {
                    detect_loops(body)
                        .loops
                        .iter()
                        .flat_map(|info| info.body_blocks.iter().copied())
                        .collect()
                } else {
                    HashSet::new()
                };
                self.out = Some(body_returns_a_stale_store_read(tcx, body, &loop_blocks));
                break;
            }
            Compilation::Stop
        }
    }

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_return_sink_{}_{}",
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
        "trust_wp_return_sink_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = C {
        fn_name: fn_name.to_string(),
        loop_lane,
        out: None,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);
    callbacks
        .out
        .unwrap_or_else(|| panic!("failed to locate function `{fn_name}` in rustc callback"))
}

/// A store in the loop body is the loop lane's: the value returned after the
/// loop is read from its exit state, so the store owes no marker there, and it
/// still trips the loop-free sink (closure_param_loop_write_ensures_stale_entry_fact).
#[test]
fn a_store_in_the_loop_body_is_left_to_the_loop_lane() {
    let source = "pub fn f(y: &mut u32) -> u32 {
        let mut i = 0u32; while i < 1 { *y = 3; i += 1; } *y }";
    assert!(!trips_the_sink(source, "f", true));
    assert!(trips_the_sink(source, "f", false));
}

/// A store before or after the loop is in no loop VC, so the loop function's
/// obligations keep the marker (loop_return_param_pointee_stored_{before,after}_loop).
#[test]
fn a_store_outside_every_loop_keeps_the_marker() {
    let before = "pub fn f(a: &mut u32) -> u32 {
        *a = 7; let mut i = 0u32; while i < 3 { i += 1; } *a }";
    let after = "pub fn f(a: &mut u32) -> u32 {
        let mut i = 0u32; while i < 3 { i += 1; } *a = 7; *a }";
    assert!(trips_the_sink(before, "f", true));
    assert!(trips_the_sink(after, "f", true));
}
