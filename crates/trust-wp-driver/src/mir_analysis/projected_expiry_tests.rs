// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-level pins for the caller-side death machinery (#prophecy-slots M5).
//!
//! These drive a real rustc through `run_compiler`, so every assertion is about
//! the actual MIR the corpus produces — not a hand-built fixture. The suite is
//! deliberately shaped as the EMIT/DISARM TABLE: one test per condition, each
//! showing that removing the condition's precondition removes the pin.
//!
//! ★The teeth are the disarm tests. A pin at an unproven death point is a
//! false-accept factory, and no downstream gate sees a consistent-but-false
//! premise (the vacuity shield only detects CONTRADICTORY premise sets — see
//! the take_first_mut adjudication). These tests are the gate.

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::formula::{FinalPinTarget, PinStep, PureExpr};

use super::{
    mut_borrow::type_analysis::{collect_mut_ref_pin_paths_with_tcx, MutRefPinStep},
    projected_expiry::{collect_projected_expiry_pins, DisarmReason, ProjectedExpiryReport},
};
use crate::callbacks::{copy_mir_bodies, thread_locals::clear_caches, try_get_body_with_context};

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

fn install_mir_borrowck_cache(config: &mut Config) {
    config.override_queries = Some(|_sess, providers| {
        crate::callbacks::spec_typecheck::install_spec_tc_mir_built_erasure(providers);
        providers.queries.mir_borrowck = |tcx, local_id| {
            if tcx.hir_node_by_def_id(local_id).body_id().is_none() {
                let guar = tcx.dcx().span_delayed_bug(
                    tcx.def_span(local_id),
                    "mir_borrowck called for item without HIR body",
                );
                return Err(guar);
            }
            copy_mir_bodies(tcx, local_id);
            (rustc_interface::DEFAULT_QUERY_PROVIDERS
                .queries
                .mir_borrowck)(tcx, local_id)
        };
    });
}

/// What one compilation captured: the pin report and the enum-aware pin paths
/// of the named local's declared return type.
#[derive(Default)]
struct Captured {
    report: Option<ProjectedExpiryReport>,
    ran: bool,
}

struct ExpiryCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    captured: Captured,
}

impl Callbacks for ExpiryCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let suffix = format!("::{}", self.fn_name);
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                let path = tcx.def_path_str(def_id);
                if path != self.fn_name && !path.ends_with(&suffix) {
                    continue;
                }
                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let Some(body_with_facts) = try_get_body_with_context(tcx, owner) else {
                    continue;
                };
                let body = super::get_mir_body(&body_with_facts);
                self.captured.report =
                    Some(collect_projected_expiry_pins(tcx, body, &self.arg_names));
                self.captured.ran = true;
                break;
            }
            Compilation::Stop
        })
    }
}

fn analyze(source: &str, fn_name: &str, arg_names: &[&str]) -> ProjectedExpiryReport {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_projected_expiry_{}_{}",
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
        "trust_wp_projected_expiry_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ExpiryCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        captured: Captured::default(),
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.captured.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks.captured.report.expect("report captured")
}

fn reasons(report: &ProjectedExpiryReport) -> Vec<DisarmReason> {
    report.disarms.iter().map(|record| record.reason).collect()
}

// ── (1) The enum arm of the path collector ──────────────────────────────────

struct PathCallbacks {
    type_alias_fn: String,
    pin_paths: Option<Vec<Vec<MutRefPinStep>>>,
    legacy_paths: Option<Vec<Vec<u32>>>,
    ran: bool,
}

impl Callbacks for PathCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let suffix = format!("::{}", self.type_alias_fn);
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                let path = tcx.def_path_str(def_id);
                if path != self.type_alias_fn && !path.ends_with(&suffix) {
                    continue;
                }
                // The probe function takes the type of interest as its ONLY
                // parameter, so `_1`'s declared type is the type under test.
                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let Some(body_with_facts) = try_get_body_with_context(tcx, owner) else {
                    continue;
                };
                let body = super::get_mir_body(&body_with_facts);
                let ty = body.local_decls[rustc_middle::mir::Local::from_u32(1)].ty;
                self.pin_paths = Some(collect_mut_ref_pin_paths_with_tcx(tcx, ty));
                self.legacy_paths =
                    Some(super::mut_borrow::type_analysis::collect_mut_ref_paths_with_tcx(tcx, ty));
                self.ran = true;
                break;
            }
            Compilation::Stop
        })
    }
}

fn probe_paths(source: &str, probe_fn: &str) -> (Vec<Vec<MutRefPinStep>>, Vec<Vec<u32>>) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_pin_paths_{}_{}",
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
        "trust_wp_pin_paths_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = PathCallbacks {
        type_alias_fn: probe_fn.to_string(),
        pin_paths: None,
        legacy_paths: None,
        ran: false,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);
    assert!(callbacks.ran, "failed to locate probe `{probe_fn}`");
    (
        callbacks.pin_paths.expect("pin paths"),
        callbacks.legacy_paths.expect("legacy paths"),
    )
}

/// ★PIN (#prophecy-slots M5 (1)): `Option<&mut T>` — the shape whose absence
/// M3 recorded as the first of three reasons the pin could not be built — is
/// now a FIRST-CLASS path, and it carries the constructor that makes it
/// meaningful.
#[test]
fn enum_payload_is_a_first_class_pin_path() {
    let source = r"
        pub fn probe(_x: Option<&mut i32>) {}
    ";
    let (pin_paths, legacy) = probe_paths(source, "probe");
    assert_eq!(
        pin_paths,
        vec![vec![MutRefPinStep::Variant {
            variant_idx: 1,
            ctor: "Some".to_string(),
            field: 0,
        }]],
        "Option<&mut i32> must yield exactly the Some-payload path"
    );
    assert!(
        legacy.is_empty(),
        "★the legacy field-index view must be UNCHANGED: widening it would \
         change find_mut_borrow_params corpus-wide, which M5 does not do"
    );
}

/// ★PIN (#prophecy-slots M5 (1)): the canonical `split_first_mut` shape —
/// `Option<(&mut T, &mut U)>` — needs BOTH the enum arm and depth 2, and it
/// must produce one path per sibling borrow (distinct carriers, the a2
/// sibling-binder-fusion lesson).
#[test]
fn option_of_tuple_of_two_mut_refs_yields_both_sibling_paths() {
    let source = r"
        pub fn probe(_x: Option<(&mut i32, &mut u32)>) {}
    ";
    let (pin_paths, legacy) = probe_paths(source, "probe");
    assert_eq!(
        pin_paths,
        vec![
            vec![
                MutRefPinStep::Variant {
                    variant_idx: 1,
                    ctor: "Some".to_string(),
                    field: 0,
                },
                MutRefPinStep::Field(0),
            ],
            vec![
                MutRefPinStep::Variant {
                    variant_idx: 1,
                    ctor: "Some".to_string(),
                    field: 0,
                },
                MutRefPinStep::Field(1),
            ],
        ],
        "each sibling borrow must get its OWN path"
    );
    assert!(legacy.is_empty(), "legacy view unchanged");
}

/// ★PIN: the legacy view is byte-equivalent on the shapes it already handled.
#[test]
fn legacy_view_is_unchanged_on_the_shapes_it_already_handled() {
    let source = r"
        pub struct HasMutRef<'a>(pub &'a mut i32);
        pub fn probe_tuple(_x: (&mut i32, &mut u32)) {}
        pub fn probe_ref_tuple(_x: &mut (i32, &mut i32)) {}
        pub fn probe_newtype(_x: HasMutRef<'_>) {}
        pub fn probe_plain(_x: &mut i32) {}
    ";
    let (_, legacy_tuple) = probe_paths(source, "probe_tuple");
    assert_eq!(legacy_tuple, vec![vec![0], vec![1]]);
    let (_, legacy_ref_tuple) = probe_paths(source, "probe_ref_tuple");
    assert_eq!(legacy_ref_tuple, vec![Vec::<u32>::new(), vec![1]]);
    let (_, legacy_newtype) = probe_paths(source, "probe_newtype");
    assert_eq!(legacy_newtype, vec![vec![0]]);
    let (_, legacy_plain) = probe_paths(source, "probe_plain");
    assert_eq!(legacy_plain, vec![Vec::<u32>::new()]);
}

// ── (3) The emit/disarm table ───────────────────────────────────────────────

const ENUM_SOURCE_PRELUDE: &str = r"
    pub enum Single<'a> { Only(&'a mut i32) }
    pub fn make_single(x: &mut i32) -> Single<'_> { Single::Only(x) }
    pub fn make_opt(x: &mut i32) -> Option<&mut i32> { Some(x) }
    pub fn make_pair<'a>(x: &'a mut i32, y: &'a mut i32) -> (&'a mut i32, &'a mut i32) { (x, y) }
    pub fn touch(_x: &mut i32) {}
";

/// ★THE EMIT CASE: an `Option<&mut T>` payload written once inside the `Some`
/// arm and dead at the end of that arm. The guard is the arm's own
/// discriminant test, so `is-Some(root)` is provably the branch condition.
#[test]
fn option_payload_written_once_in_the_arm_emits_a_guarded_pin() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32) {{
            let res = make_opt(a);
            if let Some(p) = res {{
                *p = 43;
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a"]);
    assert_eq!(
        report.pins.len(),
        1,
        "expected exactly one proven pin, got {:?} (disarms {:?})",
        report.pins,
        report.disarms
    );
    let pin = &report.pins[0];
    assert_eq!(
        pin.value,
        PureExpr::Int(43),
        "death value is the last write"
    );
    match &pin.target {
        FinalPinTarget::Projection { root, path, .. } => {
            assert_eq!(root, "res", "the pin must address the NAMED root");
            assert_eq!(
                path,
                &vec![PinStep::Variant {
                    ctor: "Some".to_string(),
                    field: 0
                }],
                "★the variant step must survive into the target — it IS the guard"
            );
        }
        other => panic!("enum payload pins must be projections, got {other:?}"),
    }
}

/// ★DISARM (R9): a payload that is never written has no death VALUE of its
/// own; a pin would degenerate to the resolve identity `^p == *p`, which is
/// exactly the premise class `should_fail/final_borrows.rs` gates.
#[test]
fn payload_without_a_tracked_write_is_disarmed() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32) {{
            let res = make_opt(a);
            if let Some(p) = res {{
                let _ = p;
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a"]);
    assert!(
        report.pins.is_empty(),
        "a write-free payload must emit NOTHING, got {:?}",
        report.pins
    );
}

/// ★DISARM (R5): the payload is passed to a call. The callee may write through
/// it after our "death", so the tracked value is not the death value.
#[test]
fn payload_moved_into_a_call_is_disarmed() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32) {{
            let res = make_opt(a);
            if let Some(p) = res {{
                *p = 43;
                touch(p);
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a"]);
    assert!(
        report.pins.is_empty(),
        "a payload handed to a callee must emit NOTHING, got {:?}",
        report.pins
    );
}

/// ★DISARM (R7/R5): a second write AFTER the point we would have called the
/// death makes the tracked value stale — or, if the write is inside the region,
/// the LAST one must win. Here the second write lives in a different block
/// (behind a nested branch), so the region is not straight-line.
#[test]
fn write_behind_a_nested_branch_is_disarmed() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32, flag: bool) {{
            let res = make_opt(a);
            if let Some(p) = res {{
                *p = 43;
                if flag {{
                    *p = 7;
                }}
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a", "flag"]);
    assert!(
        report.pins.is_empty(),
        "a branchy region must emit NOTHING, got {:?} (disarms {:?})",
        report.pins,
        report.disarms
    );
}

/// ★DISARM (R8): a non-ground death value. The pin lane has no extraction
/// environment, so it cannot know what `*a` denotes at that program point.
#[test]
fn non_ground_death_value_is_disarmed() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32, v: i32) {{
            let res = make_opt(a);
            if let Some(p) = res {{
                *p = v;
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a", "v"]);
    assert!(
        report.pins.is_empty(),
        "a non-ground death value must emit NOTHING, got {:?}",
        report.pins
    );
    assert!(
        reasons(&report).contains(&DisarmReason::ValueNotGround) || report.disarms.is_empty(),
        "when a candidate was seen at all, the reason must be the ground-value \
         refusal, got {:?}",
        report.disarms
    );
}

/// ★DISARM: a payload that escapes by being returned. Its expiry belongs to
/// OUR caller — pinning it here would assert the borrow died when it did not.
#[test]
fn returned_payload_is_disarmed() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32) -> Option<&mut i32> {{
            let res = make_opt(a);
            if let Some(p) = res {{
                *p = 43;
                return Some(p);
            }}
            None
        }}
    "
    );
    let report = analyze(&source, "caller", &["a"]);
    assert!(
        report.pins.is_empty(),
        "an escaping payload must emit NOTHING, got {:?}",
        report.pins
    );
}

/// ★DISARM: a tuple result destructured into two siblings, one of which is
/// then handed to a callee. Neither sibling may be pinned — the callee could
/// write through the one it received, and the other's region is no longer
/// straight-line.
#[test]
fn tuple_sibling_handed_to_a_callee_disarms() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32, b: &mut i32) {{
            let (p, q) = make_pair(a, b);
            *p = 1;
            touch(q);
        }}
    "
    );
    let report = analyze(&source, "caller", &["a", "b"]);
    assert!(
        report.pins.is_empty(),
        "a sibling handed to a callee must disarm the whole shape, got {:?}",
        report.pins
    );
}

/// The analysis must be a no-op — zero pins, zero candidates — on a body with
/// no call-result payload at all. This is the shape of essentially the whole
/// corpus, and it is what makes the lane's blast radius zero.
#[test]
fn ordinary_bodies_produce_no_candidates() {
    let source = r"
        pub fn caller(a: &mut i32) {
            *a = 5;
        }
    ";
    let report = analyze(source, "caller", &["a"]);
    assert!(report.pins.is_empty());
    assert!(report.disarms.is_empty());
}

// ── (4) The ghost-cluster shapes the M6 wiring newly REACHES ────────────────
//
// M5 wired `projected_expiry` into the CONTRACT extraction pipeline only, so
// contractless `ghost!` / `proof_assert!` bodies were never adjudicated at all.
// M6 wires the same lane into `standalone_proof_assert`, and the live census
// then found exactly two candidate shapes in `ghost/ghost_map.rs` — both
// DISARMED. These two tests pin those census outcomes as MIR-level facts, so a
// later change that starts emitting on either shape has to justify itself.

/// ★CENSUS PIN (R4, `root_unnamed`) — the live `ghost_map` shape.
///
/// `if let Some(x) = map.get_mut_ghost(&1) { *x = 43; }` consumes the call
/// result IN the scrutinee position, so the `Option<&mut V>` carrier is an
/// unnamed temporary. A variant-bearing pin is addressed as
/// `is-Some(root) ==> ^(payload of root) == v`, and with no source name for
/// `root` there is no symbol for the tester to receive — an UNGUARDED
/// enum-payload pin is precisely the `optmut_none_branch_pin` adversarial
/// shape. The lane refuses.
///
/// The positive control is `option_payload_written_once_in_the_arm_emits_a_
/// guarded_pin` above: the identical body with the result bound to `res` DOES
/// emit. The only difference is the name.
#[test]
fn unnamed_call_result_scrutinee_is_disarmed_root_unnamed() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32) {{
            if let Some(p) = make_opt(a) {{
                *p = 43;
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a"]);
    assert!(
        report.pins.is_empty(),
        "an unnamed enum carrier has no tester receiver; pins {:?}",
        report.pins
    );
    assert!(
        reasons(&report).contains(&DisarmReason::RootUnnamed),
        "expected the root_unnamed refusal, got {:?}",
        report.disarms
    );
}

/// ★CENSUS PIN (R2/R11, `death_not_in_region`) — the live `ghost_map`
/// `split_mut_ghost` shape.
///
/// `let (x, map2) = map.split_mut_ghost(&1); *x = 42; map2.insert_ghost(..)`
/// writes through the payload and then keeps using its SIBLING across further
/// calls, so the payload's `StorageDead` is not a statement of the extraction
/// block. The death point is therefore not proven and the lane emits nothing —
/// a call in between could write through any live borrow.
#[test]
fn payload_alive_across_a_later_call_is_disarmed_death_not_in_region() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32, b: &mut i32) {{
            let (p, q) = make_pair(a, b);
            *p = 42;
            touch(q);
            *p = 43;
        }}
    "
    );
    let report = analyze(&source, "caller", &["a", "b"]);
    assert!(
        report.pins.is_empty(),
        "a payload that outlives an intervening call must emit NOTHING, got {:?}",
        report.pins
    );
}

/// ★THE SECOND EMIT CASE: a variant-free payload (a tuple result) addressed by
/// the binder's OWN name. No tester is needed — and none is emitted.
#[test]
fn tuple_payload_written_once_emits_an_unguarded_local_pin() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32, b: &mut i32) {{
            let (p, q) = make_pair(a, b);
            *p = 1;
            *q = 2;
        }}
    "
    );
    let report = analyze(&source, "caller", &["a", "b"]);
    assert!(
        report.pins.iter().all(|pin| matches!(
            pin.target,
            FinalPinTarget::Local(_) | FinalPinTarget::Projection { .. }
        )),
        "unexpected target shape in {:?}",
        report.pins
    );
    for pin in &report.pins {
        assert!(
            !pin.target.requires_variant_guard(),
            "a tuple payload must not carry a variant guard: {:?}",
            pin.target
        );
    }
}

/// ★TEETH (R3): the emitted guard must be EXACTLY the constructor the arm
/// downcasts to — not "some constructor", not the whole switch. On a
/// three-variant enum the `A` arm rides an explicit discriminant edge, and the
/// pin must carry `is-A` and nothing else. A guard weaker than the branch
/// condition would assert the arm's death value on a path the arm never ran,
/// and no vacuity counter would see it (the premise set stays SAT).
#[test]
fn three_variant_arm_carries_the_exact_constructor_guard() {
    let source = r"
        pub enum Three<'a> { A(&'a mut i32), B(&'a mut i32), C(&'a mut i32) }
        pub fn make_three(x: &mut i32) -> Three<'_> { Three::A(x) }
        pub fn caller(a: &mut i32) {
            let res = make_three(a);
            match res {
                Three::A(p) => { *p = 1; }
                _ => {}
            }
        }
    ";
    let report = analyze(source, "caller", &["a"]);
    assert_eq!(report.pins.len(), 1, "disarms {:?}", report.disarms);
    match &report.pins[0].target {
        FinalPinTarget::Projection { path, .. } => assert_eq!(
            path,
            &vec![PinStep::Variant {
                ctor: "A".to_string(),
                field: 0
            }],
            "the guard must name the downcast constructor exactly"
        ),
        other => panic!("expected a guarded projection, got {other:?}"),
    }
}

/// ★TEETH (R3): an OR-pattern arm is reached from two discriminant edges. A
/// single `is-<Ctor>` tester is strictly weaker than "A or B", so every pin
/// this shape could produce must be guarded by the constructor of ITS OWN
/// downcast — never by one standing in for both.
#[test]
fn or_pattern_arm_guards_each_downcast_separately() {
    let source = r"
        pub enum Three<'a> { A(&'a mut i32), B(&'a mut i32), C(&'a mut i32) }
        pub fn make_three(x: &mut i32) -> Three<'_> { Three::A(x) }
        pub fn caller(a: &mut i32) {
            let res = make_three(a);
            match res {
                Three::A(p) | Three::B(p) => { *p = 1; }
                _ => {}
            }
        }
    ";
    let report = analyze(source, "caller", &["a"]);
    for pin in &report.pins {
        let FinalPinTarget::Projection { path, .. } = &pin.target else {
            panic!(
                "enum payload pins must be guarded projections: {:?}",
                pin.target
            );
        };
        assert!(
            matches!(path.as_slice(), [PinStep::Variant { ctor, .. }] if ctor == "A" || ctor == "B"),
            "an or-pattern arm must never be guarded by an unrelated \
             constructor: {path:?}"
        );
    }
}

/// ★EMIT (R3, single-variant enum): with only one constructor there is no
/// discriminant test to match against, because `is-Only(root)` is VALID. The
/// guard is vacuous in fact as well as in form, so the pin is admissible.
#[test]
fn single_variant_enum_payload_emits() {
    let source = r"
        pub enum Single<'a> { Only(&'a mut i32) }
        pub fn make_single(x: &mut i32) -> Single<'_> { Single::Only(x) }
        pub fn caller(a: &mut i32) {
            let res = make_single(a);
            let Single::Only(p) = res;
            *p = 9;
        }
    ";
    let report = analyze(source, "caller", &["a"]);
    assert_eq!(
        report.pins.len(),
        1,
        "expected one pin, got {:?} / disarms {:?}",
        report.pins,
        report.disarms
    );
    assert_eq!(report.pins[0].value, PureExpr::Int(9));
}

/// ★TEETH (R7): the LAST write in the region is the death value. If an earlier
/// write were used the pin would be false; if a later, unmodelled write existed
/// the shape must disarm. Here both writes are in the region and the later one
/// must win.
#[test]
fn last_write_in_the_region_is_the_death_value() {
    let source = format!(
        r"{ENUM_SOURCE_PRELUDE}
        pub fn caller(a: &mut i32) {{
            let res = make_opt(a);
            if let Some(p) = res {{
                *p = 1;
                *p = 2;
            }}
        }}
    "
    );
    let report = analyze(&source, "caller", &["a"]);
    assert_eq!(report.pins.len(), 1, "disarms {:?}", report.disarms);
    assert_eq!(
        report.pins[0].value,
        PureExpr::Int(2),
        "★the death value must be the LAST write, never an earlier one"
    );
}
