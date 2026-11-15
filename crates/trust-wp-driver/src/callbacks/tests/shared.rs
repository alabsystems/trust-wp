// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

const TEST_CRATE_NAME: &str = "trust_wp_callbacks_structural_rewrite_test";
static TEST_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

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

pub(super) fn find_arm<'a>(arms: &'a [MatchArm], name: &str) -> &'a MatchArm {
    arms.iter()
        .find(|arm| {
            matches!(
                &arm.pattern,
                Pattern::Constructor { name: arm_name, .. } if arm_name == name
            )
        })
        .unwrap_or_else(|| panic!("missing match arm `{name}` in {arms:?}"))
}

#[derive(Default)]
struct ProofAssertStructuralRewriteCallbacks {
    assertion: Option<PureExpr>,
    preconditions: Vec<PureExpr>,
    ran: bool,
}

impl Callbacks for ProofAssertStructuralRewriteCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut target_def_id = None;
        let mut nonzero_type_name = None;

        for local_def_id in tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if !def_path.ends_with("use_option") {
                continue;
            }

            target_def_id = Some(def_id);
            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = sig.skip_binder();
            nonzero_type_name = sig
                .inputs()
                .iter()
                .copied()
                .find_map(|ty| find_adt_path_by_short_name(tcx, ty, "NonZero"));
            break;
        }

        let target_def_id = target_def_id.expect("target function def_id");
        let nonzero_type_name = nonzero_type_name.expect("NonZero type path");
        let type_invariant_defs = vec![trust_wp_core::type_invariant_def! {
            type_name: nonzero_type_name,
            self_param: "self".to_string(),
            param_sort: None,
            body: PureExpr::Bool(true),
            is_newtype: false,
            element_invariant_method: None,
        }];

        let mut assertion = PureExpr::LogicFnCall {
            name: "inv".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        let mut preconditions = vec![assertion.clone()];

        apply_type_and_field_rewrites(
            tcx,
            target_def_id,
            &[String::from("x")],
            &type_invariant_defs,
            false,
            &mut assertion,
            &mut preconditions,
        )
        .expect("the test fixture declares no unresolvable named-field pattern");

        self.assertion = Some(assertion);
        self.preconditions = preconditions;
        self.ran = true;
        Compilation::Stop
    }
}

pub(super) fn collect_structural_proof_assert_rewrite(source: &str) -> (PureExpr, Vec<PureExpr>) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_callbacks_structural_rewrite_{}_{}",
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

    let mut callbacks = ProofAssertStructuralRewriteCallbacks::default();
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate proof-assert structural rewrite fixture"
    );
    (
        callbacks.assertion.expect("rewritten assertion"),
        callbacks.preconditions,
    )
}
