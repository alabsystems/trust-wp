// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared helpers for type invariant tests.

use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::super::{
    build_newtype_param_set, build_type_invariant_clauses, build_type_invariant_method_map,
    build_type_invariant_structural_expr_map, type_path_short_name,
};

pub(super) const TEST_CRATE_NAME: &str = "trust_wp_type_invariant_map_test";
pub(super) static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

pub(super) fn find_adt_path_by_short_name<'tcx>(
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
            if type_path_short_name(&path) == short_name {
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

pub(super) struct MethodMapCallbacks {
    pub(super) fn_name: String,
    pub(super) arg_names: Vec<String>,
    pub(super) param_methods: Option<HashMap<String, String>>,
    pub(super) ran: bool,
}

impl Callbacks for MethodMapCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = sig.skip_binder();
            let sum10_type_name = sig
                .inputs()
                .iter()
                .find_map(|ty| find_adt_path_by_short_name(tcx, *ty, "Sum10"));
            let Some(sum10_type_name) = sum10_type_name else {
                continue;
            };

            let invariant_defs = vec![trust_wp_core::type_invariant_def! {
                type_name: sum10_type_name,
                self_param: "self".to_string(),
                param_sort: None,
                body: PureExpr::Bool(true),
                is_newtype: false,
                element_invariant_method: None,
            }];

            let (param_methods, _) =
                build_type_invariant_method_map(tcx, def_id, &self.arg_names, &invariant_defs);
            self.param_methods = Some(param_methods);
            self.ran = true;
            break;
        }
        Compilation::Stop
    }
}

pub(super) fn collect_param_method_map(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
) -> HashMap<String, String> {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_type_invariant_map_{}_{}",
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

    let mut callbacks = MethodMapCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        param_methods: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .param_methods
        .expect("method map should be collected")
}

pub(super) struct ClauseCallbacks {
    pub(super) fn_name: String,
    pub(super) arg_names: Vec<String>,
    pub(super) invariant_short_names: Vec<String>,
    pub(super) invariant_requires: Option<Vec<PureExpr>>,
    pub(super) invariant_ensures: Option<Vec<PureExpr>>,
    pub(super) ran: bool,
}

impl Callbacks for ClauseCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = sig.skip_binder();
            let mut seen = HashSet::new();
            let invariant_defs: Vec<_> = self
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
            if invariant_defs.is_empty() {
                continue;
            }

            let (reqs, enss) =
                build_type_invariant_clauses(tcx, def_id, &self.arg_names, &invariant_defs);
            self.invariant_requires = Some(reqs);
            self.invariant_ensures = Some(enss);
            self.ran = true;
            break;
        }
        Compilation::Stop
    }
}

pub(super) struct StructuralRewriteCallbacks {
    pub(super) fn_name: String,
    pub(super) arg_names: Vec<String>,
    pub(super) invariant_short_names: Vec<String>,
    pub(super) target_name: String,
    pub(super) rewritten: Option<PureExpr>,
    pub(super) ran: bool,
}

impl Callbacks for StructuralRewriteCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = sig.skip_binder();
            let mut seen = HashSet::new();
            let invariant_defs: Vec<_> = self
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
            if invariant_defs.is_empty() {
                continue;
            }

            let (param_methods, result_method) =
                build_type_invariant_method_map(tcx, def_id, &self.arg_names, &invariant_defs);
            let (param_structural_exprs, result_structural_expr) =
                build_type_invariant_structural_expr_map(
                    tcx,
                    def_id,
                    &self.arg_names,
                    &invariant_defs,
                );
            let expr = PureExpr::LogicFnCall {
                name: "inv".to_string(),
                args: vec![PureExpr::Var(self.target_name.clone(), None)],
            };
            self.rewritten = Some(
                super::super::rewrite_type_invariant_methods_expr_with_structural(
                    &expr,
                    &param_methods,
                    result_method.as_deref(),
                    &param_structural_exprs,
                    result_structural_expr.as_ref(),
                ),
            );
            self.ran = true;
            break;
        }
        Compilation::Stop
    }
}

pub(super) struct NewtypeParamSetCallbacks {
    pub(super) fn_name: String,
    pub(super) arg_names: Vec<String>,
    pub(super) invariant_is_newtype: bool,
    pub(super) newtype_params: Option<HashSet<String>>,
    pub(super) ran: bool,
}

impl Callbacks for NewtypeParamSetCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = sig.skip_binder();
            let positive_u32_type_name = sig
                .inputs()
                .iter()
                .copied()
                .chain(std::iter::once(sig.output()))
                .find_map(|ty| find_adt_path_by_short_name(tcx, ty, "PositiveU32"));
            let Some(type_name) = positive_u32_type_name else {
                continue;
            };

            let invariant_defs = vec![trust_wp_core::type_invariant_def! {
                type_name: type_name,
                self_param: "self".to_string(),
                param_sort: None,
                body: PureExpr::Bool(true),
                is_newtype: self.invariant_is_newtype,
                element_invariant_method: None,
            }];
            self.newtype_params = Some(build_newtype_param_set(
                tcx,
                def_id,
                &self.arg_names,
                &invariant_defs,
            ));
            self.ran = true;
            break;
        }
        Compilation::Stop
    }
}

pub(super) fn collect_type_invariant_clauses(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
) -> (Vec<PureExpr>, Vec<PureExpr>) {
    collect_type_invariant_clauses_with_invariants(source, fn_name, arg_names, &["Sum10"])
}

pub(super) fn collect_type_invariant_clauses_with_invariants(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    invariant_short_names: &[&str],
) -> (Vec<PureExpr>, Vec<PureExpr>) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_type_invariant_clause_{}_{}",
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

    let mut callbacks = ClauseCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        invariant_short_names: invariant_short_names
            .iter()
            .map(|name| (*name).to_string())
            .collect(),
        invariant_requires: None,
        invariant_ensures: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    (
        callbacks
            .invariant_requires
            .expect("invariant_requires should be collected"),
        callbacks
            .invariant_ensures
            .expect("invariant_ensures should be collected"),
    )
}

pub(super) fn rewrite_inv_from_source(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    invariant_short_names: &[&str],
    target_name: &str,
) -> PureExpr {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_type_invariant_rewrite_{}_{}",
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

    let mut callbacks = StructuralRewriteCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        invariant_short_names: invariant_short_names
            .iter()
            .map(|name| (*name).to_string())
            .collect(),
        target_name: target_name.to_string(),
        rewritten: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .rewritten
        .expect("rewritten structural invariant should be collected")
}

pub(super) fn collect_newtype_param_set(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
) -> HashSet<String> {
    collect_newtype_param_set_with_invariant_flag(source, fn_name, arg_names, false)
}

pub(super) fn collect_newtype_param_set_with_invariant_flag(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    invariant_is_newtype: bool,
) -> HashSet<String> {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_type_invariant_newtype_{}_{}",
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

    let mut callbacks = NewtypeParamSetCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        invariant_is_newtype,
        newtype_params: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .newtype_params
        .expect("newtype param set should be collected")
}

pub(super) fn find_arm<'a>(arms: &'a [MatchArm], variant_name: &str) -> &'a MatchArm {
    arms.iter()
        .find(|arm| {
            matches!(
                &arm.pattern,
                Pattern::Constructor { name, .. } if name == variant_name
            )
        })
        .unwrap_or_else(|| panic!("missing {variant_name} arm in {arms:?}"))
}
