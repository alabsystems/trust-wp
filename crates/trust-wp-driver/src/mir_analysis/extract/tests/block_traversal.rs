// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `block_must_early_return` and `block_must_diverge` MIR
//! traversal helpers. These functions detect early-return and divergent paths
//! in MIR control flow, used by `handle_int_switch_with_context` to skip
//! try-operator (`?`) break paths during extraction.
//!
//! Part of #1276.

use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::BasicBlock;

use super::*;

static TRAVERSAL_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Results from running block traversal helpers on a compiled function.
struct TraversalResults {
    /// `block_must_early_return` result starting from bb0 (entry block).
    entry_early_return: bool,
    /// `block_must_diverge` result starting from bb0 (entry block).
    entry_must_diverge: bool,
    /// Per-block results: (block_index, terminator_kind, early_return, must_diverge).
    block_details: Vec<(u32, String, bool, bool)>,
}

struct BlockTraversalCallbacks {
    fn_name: String,
    results: Option<TraversalResults>,
    ran: bool,
}

impl Callbacks for BlockTraversalCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let bb0 = BasicBlock::from_u32(0);

            let entry_early_return = block_must_early_return(body, bb0, &mut HashSet::new());
            let entry_must_diverge = block_must_diverge(body, bb0, &mut HashSet::new());

            let mut block_details = Vec::new();
            for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                let term_kind = format!("{:?}", bb_data.terminator().kind)
                    .split('(')
                    .next()
                    .unwrap_or("Unknown")
                    .split('{')
                    .next()
                    .unwrap_or("Unknown")
                    .trim()
                    .to_string();
                let er = block_must_early_return(body, bb, &mut HashSet::new());
                let div = block_must_diverge(body, bb, &mut HashSet::new());
                block_details.push((bb.as_u32(), term_kind, er, div));
            }

            self.results = Some(TraversalResults {
                entry_early_return,
                entry_must_diverge,
                block_details,
            });
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn check_block_traversal(source: &str, fn_name: &str) -> TraversalResults {
    let unique = TRAVERSAL_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_block_traversal_{}_{}",
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
        "trust_wp_block_traversal_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = BlockTraversalCallbacks {
        fn_name: fn_name.to_string(),
        results: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .results
        .expect("results should be set when ran=true")
}

// ---------------------------------------------------------------------------
// AC1: Unit tests for block_must_early_return
// ---------------------------------------------------------------------------

// Return terminator: trivial function that returns a constant.
// Optimized MIR: bb0 has a Return terminator → early_return = true.
#[test]
fn early_return_simple_return_terminator() {
    let source = "pub fn target() -> i32 { 42 }";
    let results = check_block_traversal(source, "target");
    assert!(
        results.entry_early_return,
        "simple return function should be detected as early-return from entry, \
         blocks: {:?}",
        results.block_details
    );
    assert!(
        !results.entry_must_diverge,
        "simple return function should NOT diverge"
    );
}

// Goto chain: blocks with Goto terminators that lead to Return are
// detected as early-return when checked individually (fresh visited set).
// Note: from the entry SwitchInt, the shared visited set causes converging
// branches to return false — this is correct for the shared-visited
// semantics. The real use site calls per-branch with fresh sets.
#[test]
fn early_return_goto_chain_to_return() {
    let source = r#"
pub fn target(x: bool) -> i32 {
    let r;
    if x { r = 1; } else { r = 2; }
    r
}
"#;
    let results = check_block_traversal(source, "target");
    // Individual Goto blocks that lead to Return should be early-return.
    let goto_blocks: Vec<_> = results
        .block_details
        .iter()
        .filter(|(_, kind, _, _)| kind.starts_with("goto"))
        .collect();
    assert!(
        !goto_blocks.is_empty(),
        "expected Goto blocks in MIR, blocks: {:?}",
        results.block_details
    );
    for (idx, kind, er, _) in &goto_blocks {
        assert!(
            *er,
            "Goto block bb{idx} ({kind}) should be early-return when checked \
             individually, blocks: {:?}",
            results.block_details
        );
    }
}

// SwitchInt with all branches returning: match expression where every arm
// produces a value. Each individual branch target block should be
// early-return when checked with a fresh visited set.
//
// Note: from entry with shared visited set, the SwitchInt returns false
// because converging branches mark the merge point as visited. The real
// use site (handle_int_switch_with_context) calls per-branch with fresh
// HashSet::new(), matching the per-block results.
#[test]
fn early_return_switchint_all_branches_return() {
    let source = r#"
pub fn target(x: u32) -> i32 {
    match x {
        0 => 10,
        1 => 20,
        _ => 30,
    }
}
"#;
    let results = check_block_traversal(source, "target");
    // Every non-entry block should be early-return (they all lead to Return).
    let non_entry: Vec<_> = results
        .block_details
        .iter()
        .filter(|(idx, _, _, _)| *idx != 0)
        .collect();
    for (idx, kind, er, _) in &non_entry {
        assert!(
            *er,
            "branch target bb{idx} ({kind}) should be early-return, \
             blocks: {:?}",
            results.block_details
        );
    }
    // Verify entry IS a SwitchInt (the pattern we're testing).
    let entry = &results.block_details[0];
    assert!(
        entry.1.starts_with("switchInt"),
        "entry block should be SwitchInt, got: {}",
        entry.1
    );
}

// SwitchInt with one divergent branch: one match arm panics.
// From the entry block, block_must_early_return should be false because
// the panic branch does NOT reach Return.
#[test]
fn early_return_switchint_one_branch_panics() {
    let source = r#"
pub fn target(x: u32) -> i32 {
    match x {
        0 => panic!("bad input"),
        _ => 42,
    }
}
"#;
    let results = check_block_traversal(source, "target");
    assert!(
        !results.entry_early_return,
        "match with a panic branch should NOT be early-return from entry \
         (panic path does not reach Return), blocks: {:?}",
        results.block_details
    );
}

// Call with normal return path: a function call (String::from) that returns
// normally. The Call terminator has target: Some(next_bb), and the chain
// from entry through Call → Drop → Return should all be early-return = true.
#[test]
fn early_return_call_with_return_path() {
    let source = r#"
pub fn target(x: &str) -> String {
    String::from(x)
}
"#;
    let results = check_block_traversal(source, "target");
    assert!(
        results.entry_early_return,
        "function with Call → Return should be early-return from entry, \
         blocks: {:?}",
        results.block_details
    );
}

// Drop terminator: String parameter is dropped after extracting its length.
// MIR generates Drop terminators for owned values going out of scope.
#[test]
fn early_return_drop_then_return() {
    let source = r#"
pub fn target(s: String) -> usize {
    s.len()
}
"#;
    let results = check_block_traversal(source, "target");
    assert!(
        results.entry_early_return,
        "function with Drop → Return should be early-return from entry, \
         blocks: {:?}",
        results.block_details
    );
    // Verify at least one block has a Drop-like terminator in the path.
    // Debug format uses lowercase "drop" for Drop terminators.
    let has_drop = results
        .block_details
        .iter()
        .any(|(_, kind, _, _)| kind.to_lowercase().starts_with("drop"));
    assert!(
        has_drop,
        "expected at least one Drop terminator in MIR for String parameter, \
         blocks: {:?}",
        results.block_details
    );
}

// Cycle detection: infinite loop creates a back-edge in the CFG.
// block_must_early_return should return false because the visited set
// detects the cycle and returns false (cycles are NOT early returns).
#[test]
fn early_return_cycle_detection_infinite_loop() {
    let source = r#"
#[allow(clippy::empty_loop)]
pub fn target() -> ! {
    loop {}
}
"#;
    let results = check_block_traversal(source, "target");
    assert!(
        !results.entry_early_return,
        "infinite loop should NOT be detected as early-return (cycle → false), \
         blocks: {:?}",
        results.block_details
    );
    assert!(
        results.entry_must_diverge,
        "infinite loop should be detected as divergent"
    );
}

// Cycle detection with conditional return: loop body has a conditional
// return path. From entry, not all paths through the SwitchInt reach
// Return without cycling, so early_return should be false.
#[test]
fn early_return_loop_with_conditional_break() {
    let source = r#"
pub fn target(x: &mut i32) -> i32 {
    loop {
        *x += 1;
        if *x > 10 {
            return *x;
        }
    }
}
"#;
    let results = check_block_traversal(source, "target");
    assert!(
        !results.entry_early_return,
        "loop with conditional break should NOT be early-return from entry \
         (back-edge creates cycle that returns false), blocks: {:?}",
        results.block_details
    );
}

// Complementary: verify block_must_diverge is false for a returning function.
#[test]
fn must_diverge_false_for_returning_function() {
    let source = "pub fn target(x: i32) -> i32 { x + 1 }";
    let results = check_block_traversal(source, "target");
    assert!(
        !results.entry_must_diverge,
        "returning function should NOT diverge"
    );
    assert!(
        results.entry_early_return,
        "returning function IS early-return"
    );
}

// Complementary: verify block_must_diverge is true for panic-only function.
#[test]
fn must_diverge_true_for_panic_function() {
    let source = r#"pub fn target() -> ! { panic!("always") }"#;
    let results = check_block_traversal(source, "target");
    assert!(
        results.entry_must_diverge,
        "panic function should diverge, blocks: {:?}",
        results.block_details
    );
    assert!(
        !results.entry_early_return,
        "panic function should NOT be early-return"
    );
}

// ---------------------------------------------------------------------------
// AC2: Integration test — try-operator early-return skipping
// ---------------------------------------------------------------------------

/// Integration test: extraction of a function using the try operator (`?`).
///
/// The `?` desugaring creates a SwitchInt where one branch calls
/// `FromResidual::from_residual()` then returns (early-return path) and
/// the other continues with the unwrapped value. `handle_int_switch_with_context`
/// uses `block_must_early_return` to identify and skip the break path,
/// allowing extraction of the continue path.
///
/// We verify extraction succeeds by running `extract_return_expr_with_context`.
struct TryOperatorExtractionCallbacks {
    fn_name: String,
    extraction_succeeded: Option<bool>,
    ran: bool,
}

impl Callbacks for TryOperatorExtractionCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names: Vec<String> = vec!["x".to_string()];
            let (expr, _effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
            );

            self.extraction_succeeded = Some(expr.is_some());
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

#[test]
fn try_operator_extraction_succeeds_via_early_return_skipping() {
    let unique = TRAVERSAL_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_try_extract_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source = r#"
pub fn target(x: Option<i32>) -> Option<i32> {
    let v = x?;
    Some(v + 1)
}
"#;
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_try_extract_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = TryOperatorExtractionCallbacks {
        fn_name: "target".to_string(),
        extraction_succeeded: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `target` for try-operator extraction test"
    );
    assert!(
        callbacks.extraction_succeeded.unwrap_or(false),
        "extraction of try-operator function should succeed — \
         block_must_early_return should identify the `?` break path, \
         allowing handle_int_switch_with_context to skip it"
    );
}
