// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-loop merge havoc and unmodeled-exit detection on real MIR.

use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::atomic::Ordering,
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::{
    mir::{Local, TerminatorKind},
    ty::TyCtxt,
};

use super::{
    super::{detect_loops, every_return_passes_through, extract_loop_body, CallSpecContext},
    TEST_COUNTER,
};
use crate::mir_analysis::{
    extract::{compute_skipped_loop_merges, loop_exit_edge, region_effects},
    loop_condition_exit_write, loop_has_unmodeled_exit, loop_lane_exit, LaneExit,
};

#[derive(Debug, Default)]
struct Facts {
    loops: usize,
    unmodeled_exit: Vec<bool>,
    merge_blocks: usize,
    merge_locals: HashSet<usize>,
    unmerged_return: bool,
    /// Locals written by each loop's region (parameters included only when
    /// their own storage is written).
    region_writes: Vec<HashSet<usize>>,
    /// Whether every return passes through each loop's header.
    on_every_return: Vec<bool>,
    /// Whether each loop's path from its header to its exit switch writes
    /// what the code after the loop reads.
    condition_exit_write: Vec<bool>,
    /// Whether the first switch after each loop's header has an exit arm.
    first_switch_exits: Vec<bool>,
    /// The exit each loop's lane reads (`loop_lane_exit`).
    lane_exit: Vec<LaneExit>,
}

struct MergeCallbacks {
    fn_name: String,
    arg_count: usize,
    facts: Option<Facts>,
}

impl Callbacks for MergeCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            if tcx.def_path_str(local_def_id) != self.fn_name {
                continue;
            }
            let body = tcx.optimized_mir(local_def_id.to_def_id()).clone();
            let analysis = detect_loops(&body);
            let merges = compute_skipped_loop_merges(&body, &analysis, self.arg_count);
            let mut facts = Facts {
                loops: analysis.loops.len(),
                unmerged_return: merges.unmerged_return,
                merge_blocks: merges.havoc_at.len(),
                ..Facts::default()
            };
            for (locals, _) in merges.havoc_at.values() {
                facts
                    .merge_locals
                    .extend(locals.iter().map(|l| l.as_usize()));
            }
            let (user_specs, trait_specs, extern_specs) =
                (HashMap::new(), HashMap::new(), HashMap::new());
            let call_spec_ctx = CallSpecContext {
                tcx,
                user_specs: &user_specs,
                trait_specs: &trait_specs,
                extern_specs: &extern_specs,
            };
            let arg_names: Vec<String> = (0..self.arg_count).map(|i| format!("a{i}")).collect();
            for info in &analysis.loops {
                // The exit the extractor reads, as `extraction.rs` resolves it.
                let condition_switch = extract_loop_body(
                    &body,
                    &arg_names,
                    info,
                    Some(&analysis.loops),
                    Some(&call_spec_ctx),
                )
                .condition_switch;
                let lane = loop_lane_exit(&body, info, condition_switch);
                facts.lane_exit.push(lane);
                facts
                    .first_switch_exits
                    .push(loop_exit_edge(&body, info).is_some());
                let edge = match lane {
                    LaneExit::Edge(switch, exit) => Some((switch, exit)),
                    LaneExit::Never | LaneExit::Unresolved => None,
                };
                facts
                    .unmodeled_exit
                    .push(edge.is_some_and(|edge| loop_has_unmodeled_exit(&body, info, edge)));
                let (written, _) = region_effects(&body, self.arg_count, &info.body_blocks);
                facts
                    .region_writes
                    .push(written.iter().map(|l: &Local| l.as_usize()).collect());
                facts
                    .on_every_return
                    .push(every_return_passes_through(&body, info));
                facts.condition_exit_write.push(edge.is_some_and(|edge| {
                    loop_condition_exit_write(tcx, &body, info, edge).is_some()
                }));
            }
            // Sanity: the body really returns.
            assert!(body
                .basic_blocks
                .iter()
                .any(|bb| matches!(bb.terminator().kind, TerminatorKind::Return)));
            self.facts = Some(facts);
        }
        Compilation::Stop
    }
}

fn facts_for(source: &str, fn_name: &str, arg_count: usize) -> Facts {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_merges_{}_{}",
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
        "trust_wp_loop_merges_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = MergeCallbacks {
        fn_name: fn_name.to_string(),
        arg_count,
        facts: None,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);
    callbacks.facts.expect("function found")
}

#[test]
fn plain_while_has_no_merge_and_no_unmodeled_exit() {
    let facts = facts_for(
        "pub fn f() -> i32 { let mut x = 0; while x < 5 { x += 1; } x }",
        "f",
        0,
    );
    assert_eq!(facts.loops, 1);
    assert_eq!(facts.unmodeled_exit, vec![false]);
    assert_eq!(facts.merge_blocks, 0);
    assert!(!facts.unmerged_return);
}

#[test]
fn break_path_write_is_havocked_at_the_join() {
    // w07/v01: `x = 5; break` lies outside the back-edge blocks.
    let facts = facts_for(
        "pub fn f() -> i32 { let mut x = 0; let mut i = 0; \
         while i < 10 { if i == 3 { x = 5; break; } i += 1; } x }",
        "f",
        0,
    );
    assert_eq!(facts.unmodeled_exit, vec![true]);
    assert!(facts.merge_blocks >= 1);
    assert!(
        facts.merge_locals.contains(&1),
        "x (_1) re-bound at the merge: {facts:?}"
    );
}

#[test]
fn in_loop_return_is_an_unmodeled_exit_and_havocs_the_return_place() {
    // v05: `_0 = 7; goto return_block`.
    let facts = facts_for(
        "pub fn f() -> i32 { let mut i = 0; while i < 10 { if i == 3 { return 7; } i += 1; } 0 }",
        "f",
        0,
    );
    assert_eq!(facts.unmodeled_exit, vec![true]);
    assert!(
        facts.merge_locals.contains(&0) || facts.unmerged_return,
        "the return place is re-bound or the result is unconstrained: {facts:?}"
    );
}

#[test]
fn exit_side_write_skipped_by_a_second_break_is_havocked() {
    // x03: the resolved exit arm `y = 3; break` writes before the join that
    // the `i == 5` break reaches directly.
    let facts = facts_for(
        "pub fn f() -> i32 { let mut y = 0; let mut i = 0; \
         loop { if i >= 10 { y = 3; break; } if i == 5 { break; } i += 1; } y }",
        "f",
        0,
    );
    assert_eq!(facts.unmodeled_exit, vec![true]);
    assert!(
        facts.merge_locals.contains(&1),
        "y (_1) re-bound at the join: {facts:?}"
    );
}

#[test]
fn by_value_parameter_writes_are_region_writes_but_deref_writes_are_not() {
    // v03 / x08: whole and projected writes to a by-value parameter.
    let whole = facts_for(
        "pub fn f(mut x: i32) -> i32 { while x < 5 { x += 1; } x }",
        "f",
        1,
    );
    assert!(whole.region_writes[0].contains(&1), "{whole:?}");
    let field = facts_for(
        "pub fn f(mut p: (i32, i32)) -> i32 { let mut i = 0; while i < 3 { p.0 = 5; i += 1; } p.0 }",
        "f",
        1,
    );
    assert!(field.region_writes[0].contains(&1), "{field:?}");
    // A write THROUGH a `&mut` parameter does not re-bind the reference.
    let through = facts_for(
        "pub fn f(x: &mut i32) { let mut i = 0; while i < 3 { *x = 5; i += 1; } }",
        "f",
        1,
    );
    assert!(!through.region_writes[0].contains(&1), "{through:?}");
}

#[test]
fn mutable_borrow_of_a_by_value_parameter_is_a_region_write() {
    // x07 / v08: `set5(&mut x)` changes the parameter's own storage.
    let facts = facts_for(
        "fn set5(x: &mut i32) { *x = 5; } \
         pub fn f(mut x: i32) -> i32 { let mut i = 0; while i < 3 { set5(&mut x); i += 1; } x }",
        "f",
        1,
    );
    assert!(facts.region_writes[0].contains(&1), "{facts:?}");
}

#[test]
fn panic_unwind_and_imaginary_edges_are_not_loop_exits() {
    // 100doors: an indexing panic site in a nested loop unwinds into cleanup
    // blocks shared with the post-loop drop; that is not a join.
    let nested = facts_for(
        "pub fn f() { let mut v: Vec<bool> = vec![false; 100]; \
         for pass in 1..101usize { let mut d = pass; \
         while d <= 100 { v[d - 1] = !v[d - 1]; d += pass; } } }",
        "f",
        0,
    );
    assert!(nested.unmodeled_exit.iter().all(|u| !u), "{nested:?}");
    assert_eq!(nested.merge_blocks, 0, "{nested:?}");
    // lang/while_let: the pattern match's `FalseEdge` imaginary target.
    let while_let = facts_for(
        "pub fn f() { let mut a = Some(10); let b = &mut a; \
         while let Some(_) = b { *b = None; } }",
        "f",
        0,
    );
    assert_eq!(while_let.unmodeled_exit, vec![false], "{while_let:?}");
    assert_eq!(while_let.merge_blocks, 0, "{while_let:?}");
}

#[test]
fn a_real_break_stays_an_unmodeled_exit_with_panic_sites() {
    let facts = facts_for(
        "pub fn f(v: &[i32]) -> i32 { let mut x = 0; let mut i = 0; \
         while i < 10 { if v[0] == 3 { x = 5; break; } i += 1; } x }",
        "f",
        1,
    );
    assert_eq!(facts.unmodeled_exit, vec![true], "{facts:?}");
    assert!(
        facts.merge_locals.contains(&2),
        "x (_2) re-bound: {facts:?}"
    );
}

#[test]
fn a_for_loop_exits_through_its_none_arm() {
    let plain = facts_for(
        "pub fn f(n: u32) -> u32 { let mut s = 0u32; for _ in 0..n { s = s.wrapping_add(1); } s }",
        "f",
        1,
    );
    assert_eq!(plain.unmodeled_exit, vec![false], "{plain:?}");
    assert_eq!(plain.merge_blocks, 0, "{plain:?}");
    let with_break = facts_for(
        "pub fn f(n: u32) -> u32 { let mut s = 0u32; \
         for i in 0..n { if i == 3 { s = 7; break; } } s }",
        "f",
        1,
    );
    assert_eq!(with_break.unmodeled_exit, vec![true], "{with_break:?}");
    assert!(
        with_break.merge_locals.contains(&2),
        "s (_2) re-bound: {with_break:?}"
    );
}

/// A return before the loop, or a loop in one arm, returns on a path the loop
/// never saw; a loop every path runs through does not (D-224).
#[test]
fn a_return_that_skips_the_loop_is_seen() {
    let straight = facts_for(
        "pub fn f(n: u32) -> u32 { let mut i = 0; while i < n { i += 1; } i }",
        "f",
        1,
    );
    assert_eq!(straight.on_every_return, vec![true]);
    let early = facts_for(
        "pub fn f(c: bool, n: u32) -> u32 { if c { return 5; } \
         let mut i = 0; while i < n { i += 1; } i }",
        "f",
        2,
    );
    assert_eq!(early.on_every_return, vec![false]);
    let arm = facts_for(
        "pub fn f(c: bool, n: u32) -> u32 { let mut k = 7; \
         if c { let mut i = 0; while i < n { i += 1; } k = i; } k }",
        "f",
        2,
    );
    assert_eq!(arm.on_every_return, vec![false]);
}

/// The path from the header to the exit switch runs once more on the pass
/// that leaves; a write there counts only when code after the loop can read
/// it (loop_condition_block_write_before_exit_read_after.rs).
#[test]
fn a_condition_write_the_code_after_the_loop_reads_is_seen() {
    let statement = facts_for(
        "pub fn f() -> u32 { let mut n = 0u32; let mut i = 7u32; \
         while { let b = n < 3; i = 0; b } { i = 7; n += 1; } i }",
        "f",
        0,
    );
    assert_eq!(statement.condition_exit_write, vec![true]);
    let destination = facts_for(
        "pub fn f() -> bool { let mut n = 0u32; let mut b = true; \
         while { b = n < 3; b } { n += 1; } b }",
        "f",
        0,
    );
    assert_eq!(destination.condition_exit_write, vec![true]);
    let mut_argument = facts_for(
        "fn step(k: &mut u32, c: u32) -> bool { *k = 0; c < 3 } \
         pub fn f() -> u32 { let mut i = 7u32; let mut n = 0u32; \
         while step(&mut i, n) { i = 7; n = 5; } i }",
        "f",
        0,
    );
    assert_eq!(mut_argument.condition_exit_write, vec![true]);
    // `r` is re-targeted at `u` on the path, but the exit pass hands the
    // callee the `&mut x` the last body pass stored in it.
    let retargeted = facts_for(
        "fn zero(k: &mut u32) { *k = 0; } \
         pub fn f() -> u32 { let mut x = 7u32; let mut t = 0u32; let mut u = 0u32; \
         let mut n = 0u32; let mut r: &mut u32 = &mut t; \
         while { zero(r); r = &mut u; n < 3 } { n += 1; if n == 3 { r = &mut x; } } x }",
        "f",
        0,
    );
    assert_eq!(retargeted.condition_exit_write, vec![true]);
    // `h` is read by nothing after the loop, but it holds the `&mut x` the
    // callee writes through; `x` is read after the loop.
    let holder = facts_for(
        "pub struct H<'a> { r: &'a mut u32 } \
         impl<'a> H<'a> { fn reset(&mut self) { *self.r = 0; } } \
         pub fn f() -> u32 { let mut x = 7u32; let mut n = 0u32; \
         { let mut h = H { r: &mut x }; while { h.reset(); n < 3 } { n += 1; } } x }",
        "f",
        0,
    );
    assert_eq!(holder.condition_exit_write, vec![true]);
}

/// When the first switch after the header is a branch inside the condition
/// with no exit arm, the checks read the exit switch the lane takes its
/// condition from (D-234): a write the branch makes on the pass that leaves
/// is seen, a write nothing after the loop reads is not.
#[test]
fn a_condition_write_behind_a_branch_is_read_at_the_lane_exit() {
    let branch_write = facts_for(
        "pub fn f() -> u32 { let mut n = 0u32; let mut i = 7u32; \
         while { if n == 3 { i = 0 } n < 3 } { i = 7; n += 1; } i }",
        "f",
        0,
    );
    assert_eq!(branch_write.first_switch_exits, vec![false]);
    assert!(matches!(branch_write.lane_exit[..], [LaneExit::Edge(..)]));
    assert_eq!(branch_write.condition_exit_write, vec![true]);
    let break_after_branch = facts_for(
        "pub fn f() -> u32 { let mut n = 0u32; let mut i = 7u32; let mut m = 0u32; \
         loop { if n == 100 { m = 1; } i = 0; if n >= 3 { break; } i = 7; n += 1; } i + m }",
        "f",
        0,
    );
    assert_eq!(break_after_branch.first_switch_exits, vec![false]);
    assert_eq!(break_after_branch.condition_exit_write, vec![true]);
    let unread = facts_for(
        "pub fn f() -> u32 { let mut n = 0u32; let mut i = 7u32; let mut m = 0u32; \
         while { if n == 3 { m = 1 } n < 3 } { i = 7; n += 1; } i }",
        "f",
        0,
    );
    assert_eq!(unread.first_switch_exits, vec![false]);
    assert_eq!(unread.condition_exit_write, vec![false]);
    assert_eq!(unread.unmodeled_exit, vec![false]);
}

/// A loop some path leaves while no exit edge is the lane's is unresolved;
/// a loop no path leaves has no exit to read.
#[test]
fn a_loop_whose_exit_no_switch_resolves_is_unresolved() {
    let two_breaks = facts_for(
        "pub fn f() -> u32 { let mut n = 0u32; let mut m = 0u32; \
         loop { if n == 100 { m = 1; } if n >= 3 { break; } if n == 50 { break; } n += 1; } n + m }",
        "f",
        0,
    );
    assert_eq!(two_breaks.lane_exit, vec![LaneExit::Unresolved]);
    let never = facts_for(
        "pub fn f(c: bool) -> u32 { if c { return 1; } let mut n = 0u32; loop { n = n.wrapping_add(1); } }",
        "f",
        1,
    );
    assert_eq!(never.lane_exit, vec![LaneExit::Never]);
}

/// Temporaries and locals the condition alone reads, a shared borrow handed
/// to a callee, a `for` loop's `Iterator::next`, and a `&mut` of a local
/// nothing after the loop reads are no such write.
#[test]
fn a_condition_write_nothing_after_the_loop_reads_is_not() {
    let plain = facts_for(
        "pub fn f(n: u32) -> u32 { let mut i = 0; while i < n { i += 1; } i }",
        "f",
        1,
    );
    assert_eq!(plain.condition_exit_write, vec![false]);
    let block_local = facts_for(
        "pub fn f() -> u32 { let mut n = 0u32; \
         while { let t = n < 3; t } { n += 1; } n }",
        "f",
        0,
    );
    assert_eq!(block_local.condition_exit_write, vec![false]);
    let shared = facts_for(
        "pub fn f<T>(v: &[T]) -> usize { let mut i = 0; while i < v.len() { i += 1; } i }",
        "f",
        1,
    );
    assert_eq!(shared.condition_exit_write, vec![false]);
    let for_loop = facts_for(
        "pub fn f(n: u32) -> u32 { let mut s = 0u32; for k in 0..n { s = s.wrapping_add(k); } s }",
        "f",
        1,
    );
    assert_eq!(for_loop.condition_exit_write, vec![false]);
    let unread = facts_for(
        "pub fn f(n: u32) -> u32 { let mut v: Vec<u32> = Vec::new(); v.push(n); \
         let mut c = 0u32; while let Some(_) = v.pop() { c += 1; } c }",
        "f",
        1,
    );
    assert_eq!(unread.condition_exit_write, vec![false]);
    // A borrow the path makes of its own block local, handed to a callee.
    let path_borrow = facts_for(
        "fn zero(k: &mut u32) { *k = 0; } \
         pub fn f() -> u32 { let mut n = 0u32; \
         while { let mut t = 1u32; zero(&mut t); n < 3 } { n += 1; } n }",
        "f",
        0,
    );
    assert_eq!(path_borrow.condition_exit_write, vec![false]);
}
