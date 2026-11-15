// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which place does a write through a `&mut` land on?
//!
//! Each test pins one direction of one decision. The refusals matter as much
//! as the answers: a write-back aimed at the wrong place is a false accept,
//! strictly worse than the lost write it would be repairing.

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{Location, ProjectionElem, StatementKind};

use super::*;
use crate::mir_analysis::{
    governed_place::{governed_place, Governed},
    reaching_defs,
};

static GOVERNED_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// The resolver's answer for the body's first write through a `Deref`.
#[derive(Debug, PartialEq, Eq)]
enum Answer {
    Exact(u32, Vec<usize>),
    Candidates(Vec<(u32, Vec<usize>)>),
    Unknown,
}

struct GovernedAtDerefWrites {
    fn_name: String,
    answers: Vec<Answer>,
    ran: bool,
}

impl Callbacks for GovernedAtDerefWrites {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }
            let body = tcx.optimized_mir(local_def_id.to_def_id());
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                for (index, stmt) in data.statements.iter().enumerate() {
                    let StatementKind::Assign((place, _)) = &stmt.kind else {
                        continue;
                    };
                    if !place
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref))
                    {
                        continue;
                    }
                    let rd = reaching_defs::for_body(tcx, body);
                    let at = Location {
                        block: bb,
                        statement_index: index,
                    };
                    self.answers
                        .push(match governed_place(tcx, body, &rd, place, at) {
                            Governed::Exact(base, path) => Answer::Exact(base.as_u32(), path),
                            Governed::Candidates(set) => Answer::Candidates(
                                set.into_iter()
                                    .map(|(base, path)| (base.as_u32(), path))
                                    .collect(),
                            ),
                            Governed::Unknown => Answer::Unknown,
                        });
                }
            }
            self.ran = true;
            return Compilation::Stop;
        }
        Compilation::Stop
    }
}

/// Every deref write in the body, in statement order.
fn governed_writes(source: &str, fn_name: &str) -> Vec<Answer> {
    let unique = GOVERNED_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_governed_{}_{}",
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
        "trust_wp_governed_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = GovernedAtDerefWrites {
        fn_name: fn_name.to_string(),
        answers: Vec::new(),
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);
    assert!(callbacks.ran, "body `{fn_name}` was never reached");
    callbacks.answers
}

/// The body's sole deref write.
fn governed_for(source: &str, fn_name: &str) -> Answer {
    let mut answers = governed_writes(source, fn_name);
    assert_eq!(answers.len(), 1, "expected one deref write in `{fn_name}`");
    answers.pop().expect("checked")
}

/// A borrow of a FIELD names the owner AND the field: the edge map's value is
/// a bare local, so this is the answer it structurally cannot give.
#[test]
fn a_field_borrow_names_the_owner_and_the_field() {
    let source = r#"
pub struct S { pub a: i32, pub b: i32 }
pub fn k() { let mut s = S { a: 5, b: 6 }; let r = &mut s.a; *r = 7; }
"#;
    let Answer::Exact(_, path) = governed_for(source, "k") else {
        panic!("a field borrow resolves");
    };
    assert_eq!(path, vec![0]);
}

/// An explicit type annotation lowers the borrow through a temporary that
/// dies immediately. Reading the MIR rather than the edge map is what hops it.
#[test]
fn an_annotated_borrow_survives_its_dying_coercion_temporary() {
    let source = r#"
pub fn k() { let mut x = 5i32; let r: &mut i32 = &mut x; let r2 = r; *r2 = 7; }
"#;
    let Answer::Exact(_, path) = governed_for(source, "k") else {
        panic!("an annotated move resolves");
    };
    assert!(path.is_empty(), "the write lands on the whole local");
}

/// A `&mut` carried in an aggregate still names its pointee.
#[test]
fn a_borrow_carried_in_an_aggregate_names_its_pointee() {
    let source = r#"
pub fn k() { let mut x = 5i32; let t = (&mut x,); *t.0 = 7; }
"#;
    let Answer::Exact(_, path) = governed_for(source, "k") else {
        panic!("a tuple-held borrow resolves");
    };
    assert!(path.is_empty());
}

/// `*rr = &mut y` redirects `r`'s slot without ever assigning to `r`. The
/// store through the alias IS a definition of `r`, and because every store
/// through every alias of that slot resolves back to the slot itself, it is
/// folded in as one — killing the definition it replaces, so the later write
/// through the moved copy names the REDIRECTED target (`y`), not the original.
/// A slot with one store this resolver cannot pin down stays refused instead.
#[test]
fn a_slot_redirected_through_an_alias_names_the_new_target() {
    let source = r#"
pub fn k() {
    let mut x = 5i32;
    let mut y = 9i32;
    let mut r = &mut x;
    let rr = &mut r;
    *rr = &mut y;
    let r2 = r;
    *r2 = 7;
}
"#;
    // The first deref write IS the redirect (`*rr = &mut y`), which resolves
    // exactly — it writes `r`'s slot, and the write-back declines it for
    // being a slot. The one under test is the write through the moved copy:
    // `y`, the place the slot was redirected to.
    let answers = governed_writes(source, "k");
    assert_eq!(answers.last(), Some(&Answer::Exact(2, Vec::new())));
}

/// Reading through an alias is not redirecting through it: `&mut **x` is the
/// whole point of the nested spelling and must still resolve.
#[test]
fn reading_through_an_alias_still_resolves() {
    let source = r#"
pub fn k() {
    let mut v = 0i32;
    let mut r = &mut v;
    let x = &mut r;
    let inner: &mut i32 = &mut **x;
    *inner = 1;
}
"#;
    let Answer::Exact(_, path) = governed_for(source, "k") else {
        panic!("an unnested borrow resolves");
    };
    assert!(path.is_empty());
}

/// A borrow reassigned on ONE branch has two definitions reaching the write.
/// Both are enumerated, and an enumeration of two is never credit: the caller
/// may only invalidate every candidate. Picking one would be the guess this
/// resolver exists to refuse.
#[test]
fn a_conditionally_reassigned_borrow_enumerates_both_targets() {
    let source = r#"
pub fn k(c: bool) {
    let mut x = 5i32;
    let mut y = 9i32;
    let mut r = &mut x;
    if c { r = &mut y; }
    *r = 7;
}
"#;
    let Answer::Candidates(mut set) = governed_for(source, "k") else {
        panic!("a conditional reassignment enumerates both targets");
    };
    set.sort();
    assert_eq!(set, vec![(2, Vec::new()), (3, Vec::new())]);
}

/// REFUSAL. A parameter's pointee is the prophecy lane's property: `^p` is
/// credited there, and a write-back granted here would be the same fact
/// granted twice by code that does not know about the other.
#[test]
fn a_parameter_rooted_borrow_is_refused() {
    let source = r#"
pub struct S { pub a: i32, pub b: i32 }
pub fn k(p: &mut S) { let r = &mut p.a; *r = 7; }
"#;
    assert_eq!(governed_for(source, "k"), Answer::Unknown);
}

/// REFUSAL. A store INTO the aggregate can redirect the borrow the aggregate
/// hop would otherwise read straight out of the constructor.
#[test]
fn an_aggregate_written_into_after_construction_is_refused() {
    let source = r#"
pub struct H<'a> { pub p: &'a mut i32 }
pub fn k() {
    let mut x = 5i32;
    let mut y = 9i32;
    let mut h = H { p: &mut x };
    h.p = &mut y;
    *h.p = 7;
}
"#;
    assert_eq!(governed_for(source, "k"), Answer::Unknown);
}
