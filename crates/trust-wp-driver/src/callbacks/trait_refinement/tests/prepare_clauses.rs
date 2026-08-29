// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    formula::{int_bounds::signed_bounds_expr, resolve_sort_name, BinOp, ExprSort, PureExpr},
    logic::TypeInvariantDef,
};

use super::super::{
    prepare::{prepare_refinement_clauses, PreparedRefinementClauses},
    TraitRefinementRequest,
};
use crate::{
    callbacks::{
        integer_range::build_unsigned_range_preconditions, parsing::parse_contract_clauses,
    },
    contracts::TraitMethodContract,
};

const TEST_CRATE_NAME: &str = "trust_wp_trait_refinement_prepare_test";
static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

fn find_adt_path_by_short_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    short_name: &str,
) -> Option<String> {
    let inner = match ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
        _ => ty,
    };

    match inner.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
            let path = tcx.def_path_str(adt_def.did());
            if path.rsplit("::").next() == Some(short_name) {
                return Some(path);
            }
            substs
                .types()
                .find_map(|arg_ty| find_adt_path_by_short_name(tcx, arg_ty, short_name))
        }
        rustc_middle::ty::TyKind::Tuple(fields) => fields
            .iter()
            .find_map(|elem| find_adt_path_by_short_name(tcx, elem, short_name)),
        rustc_middle::ty::TyKind::Array(elem, _) | rustc_middle::ty::TyKind::Slice(elem) => {
            find_adt_path_by_short_name(tcx, *elem, short_name)
        }
        _ => None,
    }
}

#[derive(Default)]
struct PrepareRefinementCallbacks {
    prepared: Option<PreparedRefinementClauses>,
    ran: bool,
    trait_requires: Vec<String>,
    trait_ensures: Vec<String>,
    base_requires: Vec<String>,
    base_ensures: Vec<String>,
    invariant_short_names: Vec<String>,
}

impl Callbacks for PrepareRefinementCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut trait_method_def_id: Option<DefId> = None;
        let mut impl_def_id: Option<DefId> = None;
        for local_def_id in tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);

            if def_path.ends_with("InvariantRefinement::keep") && !def_path.starts_with('<') {
                trait_method_def_id = Some(def_id);
                continue;
            }

            if def_path.contains("InvariantRefinementImpl") && def_path.ends_with("::keep") {
                impl_def_id = Some(def_id);
            }
        }

        let trait_method_def_id = trait_method_def_id.expect("trait method def_id");
        let impl_def_id = impl_def_id.expect("impl method def_id");
        let sig = tcx.fn_sig(impl_def_id).instantiate_identity();
        let sig = sig.skip_binder();
        let mut seen = std::collections::HashSet::new();
        let type_invariant_defs: Vec<_> = self
            .invariant_short_names
            .iter()
            .filter_map(|short_name| {
                sig.inputs()
                    .iter()
                    .copied()
                    .chain(std::iter::once(sig.output()))
                    .find_map(|ty| find_adt_path_by_short_name(tcx, ty, short_name))
            })
            .filter(|type_name| seen.insert(type_name.clone()))
            .map(|type_name| {
                trust_wp_core::type_invariant_def! {
                    type_name: type_name,
                    self_param: "self".to_string(),
                    param_sort: None,
                    body: PureExpr::Bool(true),
                    is_newtype: false,
                    element_invariant_method: None,
                }
            })
            .collect();

        let trait_contract = TraitMethodContract {
            trait_def_id: trait_method_def_id,
            method_def_id: trait_method_def_id,
            method_name: "keep".to_string(),
            trait_path: format!("{TEST_CRATE_NAME}::InvariantRefinement"),
            requires: if self.trait_requires.is_empty() {
                vec!["true".to_string()]
            } else {
                self.trait_requires.clone()
            },
            ensures: self.trait_ensures.clone(),
        };
        let impl_arg_names = [String::from("self"), String::from("x")];
        let base_requires = parse_contract_clauses(
            &self.base_requires,
            "impl requires",
            "test::InvariantRefinementImpl::keep",
        )
        .expect("parse impl requires");
        let base_ensures = parse_contract_clauses(
            &self.base_ensures,
            "impl ensures",
            "test::InvariantRefinementImpl::keep",
        )
        .expect("parse impl ensures");
        let req = TraitRefinementRequest {
            impl_def_id,
            impl_arg_names: &impl_arg_names,
            trait_contract: &trait_contract,
            base_requires: &base_requires,
            base_ensures: &base_ensures,
            type_invariant_defs: &type_invariant_defs,
            logic_fns_opt: None,
            mode_overrides_opt: None,
            adt_decls: None,
            track_level: trust_wp_core::TrackLevel::Reg,
            def_path: "test::InvariantRefinementImpl::keep",
            loc: "test.rs:1",
            verbose: false,
        };

        self.prepared =
            Some(prepare_refinement_clauses(tcx, &req).expect("prepare refinement clauses"));
        self.ran = true;
        Compilation::Stop
    }
}

fn collect_prepared_refinement_clauses(source: &str) -> PreparedRefinementClauses {
    collect_prepared_refinement_clauses_with_contracts(source, &["true"], &[], &[], &[])
}

fn collect_prepared_refinement_clauses_with_contracts(
    source: &str,
    trait_requires: &[&str],
    trait_ensures: &[&str],
    base_requires: &[&str],
    base_ensures: &[&str],
) -> PreparedRefinementClauses {
    collect_prepared_refinement_clauses_with_contracts_and_invariants(
        source,
        trait_requires,
        trait_ensures,
        base_requires,
        base_ensures,
        &["Sum10"],
    )
}

fn collect_prepared_refinement_clauses_with_contracts_and_invariants(
    source: &str,
    trait_requires: &[&str],
    trait_ensures: &[&str],
    base_requires: &[&str],
    base_ensures: &[&str],
    invariant_short_names: &[&str],
) -> PreparedRefinementClauses {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_trait_refinement_prepare_{}_{}",
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
        TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = PrepareRefinementCallbacks {
        trait_requires: trait_requires.iter().map(ToString::to_string).collect(),
        trait_ensures: trait_ensures.iter().map(ToString::to_string).collect(),
        base_requires: base_requires.iter().map(ToString::to_string).collect(),
        base_ensures: base_ensures.iter().map(ToString::to_string).collect(),
        invariant_short_names: invariant_short_names
            .iter()
            .map(|name| (*name).to_string())
            .collect(),
        ..PrepareRefinementCallbacks::default()
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate trait refinement fixture in rustc callback"
    );
    callbacks
        .prepared
        .expect("prepared refinement clauses should be collected")
}

fn has_invariant_call(exprs: &[PureExpr], receiver_name: &str, type_fragment: &str) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && method.contains(type_fragment)
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name)
        )
    })
}

fn has_typed_invariant_call(exprs: &[PureExpr], receiver_name: &str, type_fragment: &str) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && method.contains(type_fragment)
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::Var(name, Some(ExprSort::Datatype(id)))
                            if name == receiver_name && resolve_sort_name(*id).contains(type_fragment)
                    )
        )
    })
}

fn has_deref_invariant_call(exprs: &[PureExpr], receiver_name: &str, type_fragment: &str) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && method.contains(type_fragment)
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::Deref(inner)
                            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == receiver_name)
                    )
        )
    })
}

fn has_final_invariant_call(exprs: &[PureExpr], receiver_name: &str, type_fragment: &str) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && method.contains(type_fragment)
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::Final(inner)
                            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == receiver_name)
                    )
        )
    })
}

fn has_plain_invariant_call(exprs: &[PureExpr], receiver_name: &str) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && method == "invariant"
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name)
        ) || matches!(
            expr,
            PureExpr::LogicFnCall { name, args }
                if name == "inv"
                    && matches!(&args[..], [PureExpr::Var(arg_name, _)] if arg_name == receiver_name)
        )
    })
}

fn has_structural_match_on_var(exprs: &[PureExpr], scrutinee_name: &str) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::Match { scrutinee, arms }
                if matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == scrutinee_name)
                    && !arms.is_empty()
        )
    })
}

fn has_view_var_bound(exprs: &[PureExpr], var_name: &str, op: BinOp, bound: &PureExpr) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::BinOp(lhs, expr_op, rhs)
                if *expr_op == op
                    && rhs.as_ref() == bound
                    && matches!(
                        lhs.as_ref(),
                        PureExpr::View(inner)
                            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var_name)
                    )
        )
    })
}

/// #1579 regression: refinement preparation must add type-invariant clauses to
/// both sides and normalize impl-side parameter names to the trait signature.
#[test]
fn test_prepare_refinement_clauses_adds_type_invariant_parity_with_param_normalization() {
    let source = r#"
#![allow(dead_code)]

pub struct Sum10(i32, i32);

pub trait InvariantRefinement {
    fn keep(&self, value: Sum10) -> Sum10;
}

pub struct InvariantRefinementImpl;

impl InvariantRefinement for InvariantRefinementImpl {
    fn keep(&self, x: Sum10) -> Sum10 {
        x
    }
}
"#;

    let prepared = collect_prepared_refinement_clauses(source);

    assert!(
        matches!(prepared.trait_requires.first(), Some(PureExpr::Bool(true))),
        "trait requires should preserve the user-written clause: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_invariant_call(&prepared.trait_requires, "value", "Sum10"),
        "trait side should gain a type-invariant clause on the trait parameter: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_invariant_call(&prepared.impl_requires, "value", "Sum10"),
        "impl side should gain a normalized invariant clause matching the trait name: {:?}",
        prepared.impl_requires
    );
    assert!(
        !has_invariant_call(&prepared.impl_requires, "x", "Sum10"),
        "impl invariant clause should be normalized away from the impl-only name: {:?}",
        prepared.impl_requires
    );
    assert!(
        has_invariant_call(&prepared.trait_ensures, "result", "Sum10"),
        "trait side should gain a result invariant clause: {:?}",
        prepared.trait_ensures
    );
    assert!(
        has_invariant_call(&prepared.impl_ensures, "result", "Sum10"),
        "impl side should gain a result invariant clause: {:?}",
        prepared.impl_ensures
    );
}

/// #2606 regression: refinement preparation must rewrite raw `invariant()`
/// clauses to type-qualified methods before solving.
#[test]
fn test_prepare_refinement_clauses_rewrites_user_written_invariant_methods() {
    let source = r#"
#![allow(dead_code)]

pub struct Sum10(i32, i32);

pub trait InvariantRefinement {
    fn keep(&self, value: Sum10) -> Sum10;
}

pub struct InvariantRefinementImpl;

impl InvariantRefinement for InvariantRefinementImpl {
    fn keep(&self, x: Sum10) -> Sum10 {
        x
    }
}
"#;

    let prepared = collect_prepared_refinement_clauses_with_contracts(
        source,
        &["value.invariant()"],
        &["result.invariant()"],
        &["x.invariant()"],
        &["result.invariant()"],
    );

    assert!(
        has_invariant_call(&prepared.trait_requires, "value", "Sum10"),
        "trait requires should rewrite to the Sum10-qualified invariant method: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_typed_invariant_call(&prepared.trait_requires, "value", "Sum10"),
        "trait requires should preserve the typed receiver sort for invariant dispatch: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_invariant_call(&prepared.trait_ensures, "result", "Sum10"),
        "trait ensures should rewrite to the Sum10-qualified invariant method: {:?}",
        prepared.trait_ensures
    );
    assert!(
        has_typed_invariant_call(&prepared.trait_ensures, "result", "Sum10"),
        "trait ensures should preserve the typed result sort for invariant dispatch: {:?}",
        prepared.trait_ensures
    );
    assert!(
        has_invariant_call(&prepared.impl_requires, "value", "Sum10"),
        "impl requires should rewrite before normalization and keep the trait parameter name: {:?}",
        prepared.impl_requires
    );
    assert!(
        has_typed_invariant_call(&prepared.impl_requires, "value", "Sum10"),
        "impl requires should preserve the normalized typed receiver sort: {:?}",
        prepared.impl_requires
    );
    assert!(
        has_invariant_call(&prepared.impl_ensures, "result", "Sum10"),
        "impl ensures should rewrite to the Sum10-qualified invariant method: {:?}",
        prepared.impl_ensures
    );
    assert!(
        has_typed_invariant_call(&prepared.impl_ensures, "result", "Sum10"),
        "impl ensures should preserve the typed result sort for invariant dispatch: {:?}",
        prepared.impl_ensures
    );
    assert!(
        matches!(
            prepared.result_expr.as_ref(),
            Some(PureExpr::Var(name, Some(ExprSort::Datatype(_)))) if name == "result"
        ),
        "post-refinement requests need a typed `result` binding to avoid fallback demotion: {:?}",
        prepared.result_expr
    );
    assert!(
        !has_plain_invariant_call(&prepared.trait_requires, "value"),
        "trait requires should not retain a generic invariant() call: {:?}",
        prepared.trait_requires
    );
    assert!(
        !has_plain_invariant_call(&prepared.trait_ensures, "result"),
        "trait ensures should not retain a generic invariant() call: {:?}",
        prepared.trait_ensures
    );
    assert!(
        !has_plain_invariant_call(&prepared.impl_requires, "value"),
        "impl requires should not retain a generic invariant() call after normalization: {:?}",
        prepared.impl_requires
    );
    assert!(
        !has_plain_invariant_call(&prepared.impl_ensures, "result"),
        "impl ensures should not retain a generic invariant() call: {:?}",
        prepared.impl_ensures
    );
}

/// #1296 regression: trait refinement must also rewrite structural `inv(...)`
/// contracts, not just direct invariant methods.
#[test]
fn test_prepare_refinement_clauses_rewrites_structural_inv_calls() {
    let source = r#"
#![allow(dead_code)]

pub struct NonZero(i32);
pub struct Sum10(i32, i32);

pub trait InvariantRefinement {
    fn keep(&self, value: Result<NonZero, Sum10>) -> Result<NonZero, Sum10>;
}

pub struct InvariantRefinementImpl;

impl InvariantRefinement for InvariantRefinementImpl {
    fn keep(&self, x: Result<NonZero, Sum10>) -> Result<NonZero, Sum10> {
        x
    }
}
"#;

    let prepared = collect_prepared_refinement_clauses_with_contracts_and_invariants(
        source,
        &["inv(value)"],
        &["inv(result)"],
        &["inv(x)"],
        &["inv(result)"],
        &["NonZero", "Sum10"],
    );

    assert!(
        has_structural_match_on_var(&prepared.trait_requires, "value"),
        "trait requires should rewrite to a structural match on the trait parameter: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_structural_match_on_var(&prepared.trait_ensures, "result"),
        "trait ensures should rewrite to a structural match on result: {:?}",
        prepared.trait_ensures
    );
    assert!(
        has_structural_match_on_var(&prepared.impl_requires, "value"),
        "impl requires should normalize and rewrite to a structural match on the trait name: {:?}",
        prepared.impl_requires
    );
    assert!(
        !has_structural_match_on_var(&prepared.impl_requires, "x"),
        "impl requires should not retain the impl-only parameter name after normalization: {:?}",
        prepared.impl_requires
    );
    assert!(
        has_structural_match_on_var(&prepared.impl_ensures, "result"),
        "impl ensures should rewrite to a structural match on result: {:?}",
        prepared.impl_ensures
    );
    assert!(
        !has_plain_invariant_call(&prepared.trait_requires, "value"),
        "trait requires should not retain a generic inv/value.invariant call: {:?}",
        prepared.trait_requires
    );
    assert!(
        !has_plain_invariant_call(&prepared.trait_ensures, "result"),
        "trait ensures should not retain a generic inv/result.invariant call: {:?}",
        prepared.trait_ensures
    );
    assert!(
        !has_plain_invariant_call(&prepared.impl_requires, "value"),
        "impl requires should not retain a generic inv/result.invariant call after normalization: {:?}",
        prepared.impl_requires
    );
    assert!(
        !has_plain_invariant_call(&prepared.impl_ensures, "result"),
        "impl ensures should not retain a generic inv/result.invariant call: {:?}",
        prepared.impl_ensures
    );
}

/// #2611 regression: `&mut` invariant clauses must keep trait-name
/// normalization in both the dereferenced precondition and final-value
/// postcondition shapes.
#[test]
fn test_prepare_refinement_clauses_normalizes_mut_ref_invariant_pre_and_post_clauses() {
    let source = r#"
#![allow(dead_code)]

pub struct Sum10(i32, i32);

pub trait InvariantRefinement {
    fn keep(&self, value: &mut Sum10);
}

pub struct InvariantRefinementImpl;

impl InvariantRefinement for InvariantRefinementImpl {
    fn keep(&self, x: &mut Sum10) {
        let _ = x;
    }
}
"#;

    let prepared = collect_prepared_refinement_clauses(source);

    assert!(
        matches!(prepared.trait_requires.first(), Some(PureExpr::Bool(true))),
        "trait requires should preserve the user-written clause: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_deref_invariant_call(&prepared.trait_requires, "value", "Sum10"),
        "trait side should gain a dereferenced invariant clause on the trait parameter: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_deref_invariant_call(&prepared.impl_requires, "value", "Sum10"),
        "impl side should normalize the dereferenced invariant clause to the trait name: {:?}",
        prepared.impl_requires
    );
    assert!(
        !has_deref_invariant_call(&prepared.impl_requires, "x", "Sum10"),
        "impl-side dereferenced invariant clause should be normalized away from the impl-only name: {:?}",
        prepared.impl_requires
    );
    assert!(
        has_final_invariant_call(&prepared.trait_ensures, "value", "Sum10"),
        "trait side should gain a final-value invariant clause for the mutable parameter: {:?}",
        prepared.trait_ensures
    );
    assert!(
        has_final_invariant_call(&prepared.impl_ensures, "value", "Sum10"),
        "impl side should normalize the final-value invariant clause to the trait name: {:?}",
        prepared.impl_ensures
    );
    assert!(
        !has_final_invariant_call(&prepared.impl_ensures, "x", "Sum10"),
        "impl-side final-value invariant clause should be normalized away from the impl-only name: {:?}",
        prepared.impl_ensures
    );
}

#[derive(Default)]
struct PrepareRangeParityCallbacks {
    prepared: Option<PreparedRefinementClauses>,
    ran: bool,
}

impl Callbacks for PrepareRangeParityCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut trait_method_def_id: Option<DefId> = None;
        let mut impl_def_id: Option<DefId> = None;

        for local_def_id in tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);

            if def_path.ends_with("RangeRefinement::keep") && !def_path.starts_with('<') {
                trait_method_def_id = Some(def_id);
                continue;
            }

            if def_path.contains("RangeRefinementImpl") && def_path.ends_with("::keep") {
                impl_def_id = Some(def_id);
            }
        }

        let trait_method_def_id = trait_method_def_id.expect("trait method def_id");
        let impl_def_id = impl_def_id.expect("impl method def_id");
        let impl_arg_names = [String::from("self"), String::from("x")];
        let base_requires = build_unsigned_range_preconditions(tcx, impl_def_id, &impl_arg_names);
        let type_invariant_defs: Vec<TypeInvariantDef> = Vec::new();
        let trait_contract = TraitMethodContract {
            trait_def_id: trait_method_def_id,
            method_def_id: trait_method_def_id,
            method_name: "keep".to_string(),
            trait_path: format!("{TEST_CRATE_NAME}::RangeRefinement"),
            requires: vec!["true".to_string()],
            ensures: vec![],
        };
        let req = TraitRefinementRequest {
            impl_def_id,
            impl_arg_names: &impl_arg_names,
            trait_contract: &trait_contract,
            base_requires: &base_requires,
            base_ensures: &[],
            type_invariant_defs: &type_invariant_defs,
            logic_fns_opt: None,
            mode_overrides_opt: None,
            adt_decls: None,
            track_level: trust_wp_core::TrackLevel::Reg,
            def_path: "test::RangeRefinementImpl::keep",
            loc: "test.rs:1",
            verbose: false,
        };

        self.prepared =
            Some(prepare_refinement_clauses(tcx, &req).expect("prepare refinement clauses"));
        self.ran = true;
        Compilation::Stop
    }
}

fn collect_prepared_refinement_ranges(source: &str) -> PreparedRefinementClauses {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_trait_refinement_ranges_{}_{}",
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
        TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = PrepareRangeParityCallbacks::default();
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate trait refinement range-parity fixture in rustc callback"
    );
    callbacks
        .prepared
        .expect("prepared refinement clauses should be collected")
}

/// #2363 regression: preparation must add trait-side integer ranges and
/// normalize impl-side injected ranges to trait parameter names.
#[test]
fn test_prepare_refinement_clauses_adds_integer_range_parity_with_param_normalization() {
    let source = r#"
#![allow(dead_code)]

pub trait RangeRefinement {
    fn keep(&self, value: i32) -> i32;
}

pub struct RangeRefinementImpl;

impl RangeRefinement for RangeRefinementImpl {
    fn keep(&self, x: i32) -> i32 {
        x
    }
}
"#;

    let prepared = collect_prepared_refinement_ranges(source);
    let (i32_min, i32_max) = signed_bounds_expr(32);

    assert!(
        matches!(prepared.trait_requires.first(), Some(PureExpr::Bool(true))),
        "trait requires should preserve the user-written clause: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_view_var_bound(&prepared.trait_requires, "value", BinOp::Ge, &i32_min),
        "trait side should gain the signed lower-bound clause: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_view_var_bound(&prepared.trait_requires, "value", BinOp::Le, &i32_max),
        "trait side should gain the signed upper-bound clause: {:?}",
        prepared.trait_requires
    );
    assert!(
        has_view_var_bound(&prepared.impl_requires, "value", BinOp::Ge, &i32_min),
        "impl side should keep the lower-bound clause after parameter normalization: {:?}",
        prepared.impl_requires
    );
    assert!(
        has_view_var_bound(&prepared.impl_requires, "value", BinOp::Le, &i32_max),
        "impl side should keep the upper-bound clause after parameter normalization: {:?}",
        prepared.impl_requires
    );
    assert!(
        !has_view_var_bound(&prepared.impl_requires, "x", BinOp::Ge, &i32_min)
            && !has_view_var_bound(&prepared.impl_requires, "x", BinOp::Le, &i32_max),
        "impl-side integer ranges should be normalized away from the impl-only name: {:?}",
        prepared.impl_requires
    );
}
