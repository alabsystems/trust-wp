// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::logic::type_param_invariant_index;

use super::{super::common::collect_type_invariant_clauses, *};

fn type_param_clause_on<'a>(
    reqs: &'a [PureExpr],
    receiver_is: impl Fn(&PureExpr) -> bool,
) -> Option<&'a PureExpr> {
    reqs.iter().find(|clause| {
        matches!(
            clause,
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && type_param_invariant_index(method) == Some(0)
                    && receiver_is(receiver)
        )
    })
}

fn var(expr: &PureExpr, name: &str) -> bool {
    matches!(expr, PureExpr::Var(found, _) if found == name)
}

#[test]
fn a_type_parameter_is_granted_its_opaque_invariant_at_every_holding_position() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

// `anchor` puts an invariant-bearing type in the signature: the harness
// registers definitions only for types the signature names.
pub fn generic<T>(
    by_value: T,
    shared: &T,
    unique: &mut T,
    pair: (T, i32),
    maybe: Option<T>,
    anchor: Sum10,
) {
    let _ = (by_value, shared, unique, pair, maybe, anchor);
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(
        source,
        "generic",
        &["by_value", "shared", "unique", "pair", "maybe", "anchor"],
    );

    assert!(
        type_param_clause_on(&reqs, |r| var(r, "by_value")).is_some(),
        "by-value `T`: {reqs:?}"
    );
    // A shared reference is transparent, exactly as for an ADT parameter.
    assert!(
        type_param_clause_on(&reqs, |r| var(r, "shared")).is_some(),
        "`&T`: {reqs:?}"
    );
    assert!(
        type_param_clause_on(
            &reqs,
            |r| matches!(r, PureExpr::Deref(inner) if var(inner, "unique"))
        )
        .is_some(),
        "`&mut T` holds the referent's invariant: {reqs:?}"
    );
    assert!(
        type_param_clause_on(&reqs, |r| matches!(
            r,
            PureExpr::LogicFnCall { args, .. } if args.len() == 1 && var(&args[0], "pair")
        ))
        .is_some(),
        "a tuple field typed by `T`: {reqs:?}"
    );
    let maybe = reqs
        .iter()
        .find(
            |clause| matches!(clause, PureExpr::Match { scrutinee, .. } if var(scrutinee, "maybe")),
        )
        .unwrap_or_else(|| panic!("an `Option<T>` payload: {reqs:?}"));
    let PureExpr::Match { arms, .. } = maybe else {
        unreachable!()
    };
    assert!(
        arms.iter().any(|arm| matches!(
            &arm.body,
            PureExpr::MethodCall { method, .. } if type_param_invariant_index(method) == Some(0)
        )),
        "the `Some` arm states the payload's invariant: {arms:?}"
    );

    // The final-value half of `&mut T` has no call-site reader, so it is not
    // minted as a goal of the body either.
    assert!(
        !enss
            .iter()
            .any(crate::callbacks::mentions_type_param_invariant),
        "no type-parameter ensures: {enss:?}"
    );
}

#[test]
fn a_concrete_parameter_is_granted_no_type_parameter_invariant() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn concrete(s: Sum10, n: i32, pair: (i32, u8)) {
    let _ = (s, n, pair);
}
"#;
    let (reqs, _) = collect_type_invariant_clauses(source, "concrete", &["s", "n", "pair"]);
    assert!(
        !reqs
            .iter()
            .any(crate::callbacks::mentions_type_param_invariant),
        "{reqs:?}"
    );
}

/// Per parameter of `probe`: the premise the builder grants it, and what a call
/// fixing a type parameter to that parameter's type owes over the same term.
struct InstantiationCallbacks {
    answers: Option<Vec<(Vec<PureExpr>, crate::callbacks::TypeParamInvariantAt)>>,
}

impl rustc_driver::Callbacks for InstantiationCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if !tcx.def_path_str(def_id).ends_with("probe") {
                continue;
            }
            let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
            let sum10 = sig
                .inputs()
                .iter()
                .find_map(|ty| super::super::common::find_adt_path_by_short_name(tcx, *ty, "Sum10"))
                .expect("`probe` names Sum10");
            let defs = vec![trust_wp_core::type_invariant_def! {
                type_name: sum10,
                self_param: "self".to_string(),
                param_sort: None,
                body: PureExpr::Bool(true),
                is_newtype: false,
                element_invariant_method: None,
            }];
            super::super::super::install_invariant_type_names(&defs);
            let names: Vec<String> = (0..sig.inputs().len()).map(|i| format!("p{i}")).collect();
            let (reqs, _) =
                super::super::super::build_type_invariant_clauses(tcx, def_id, &names, &defs);
            let answers = sig
                .inputs()
                .iter()
                .zip(&names)
                .map(|(ty, name)| {
                    let receiver = PureExpr::Var(
                        name.clone(),
                        crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, *ty),
                    );
                    let marker = PureExpr::MethodCall {
                        receiver: Arc::new(receiver),
                        method: trust_wp_core::logic::type_param_invariant_method_name(0, "T"),
                        args: vec![],
                    };
                    let granted = reqs
                        .iter()
                        .filter(|clause| clause.free_vars().contains(name))
                        .cloned()
                        .collect();
                    (
                        granted,
                        crate::callbacks::type_param_invariant_at(tcx, *ty, &marker),
                    )
                })
                .collect();
            crate::callbacks::clear_invariant_type_names();
            self.answers = Some(answers);
            break;
        }
        rustc_driver::Compilation::Stop
    }
}

fn instantiation_answers(
    source: &str,
) -> Vec<(Vec<PureExpr>, crate::callbacks::TypeParamInvariantAt)> {
    use std::sync::atomic::Ordering;
    let unique = super::super::common::TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_type_param_instantiation_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&temp_dir).expect("create test temp dir");
    let source_path = temp_dir.join("test.rs");
    std::fs::write(&source_path, source).expect("write test source");
    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        super::super::common::TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = InstantiationCallbacks { answers: None };
    rustc_driver::run_compiler(&args, &mut callbacks);
    let _ = std::fs::remove_dir_all(&temp_dir);
    callbacks.answers.expect("`probe` was analysed")
}

#[test]
fn a_type_argument_owes_exactly_the_premise_a_parameter_of_that_type_holds_or_refuses() {
    use crate::callbacks::TypeParamInvariantAt;
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);
#[allow(dead_code)]
pub struct Wrapper { s: Sum10 }
#[allow(dead_code)]
pub struct Plain { n: i32 }

#[allow(clippy::too_many_arguments)]
pub fn probe<U>(
    p0: Sum10,
    p1: &Sum10,
    p2: &mut Sum10,
    p3: (Sum10, i32),
    p4: Option<Sum10>,
    p5: U,
    p6: Option<U>,
    p7: Box<Sum10>,
    p8: [Sum10; 1],
    p9: Vec<Sum10>,
    p10: Wrapper,
    p11: (Option<Sum10>, Sum10),
    p12: &&Sum10,
    p13: i32,
    p14: String,
    p15: (i32, bool),
    p16: Option<i32>,
    p17: Plain,
) {
    let _ = (p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17);
}
"#;
    let answers = instantiation_answers(source);
    let conjoined = |granted: &[PureExpr]| {
        granted
            .iter()
            .cloned()
            .reduce(|l, r| PureExpr::BinOp(Arc::new(l), BinOp::And, Arc::new(r)))
    };
    // Charged: the call owes the very clauses a body at that type holds.
    for p in 0..=6 {
        let (granted, answer) = &answers[p];
        let whole = conjoined(granted).unwrap_or_else(|| panic!("p{p} is granted a premise"));
        assert_eq!(answer, &TypeParamInvariantAt::Clause(whole), "p{p}");
    }
    // Refused: some part that may carry an invariant is stated by no clause —
    // p11's builder grants `inv(p11.1)` and says nothing of the `Option`.
    for p in 7..=12 {
        assert_eq!(
            answers[p].1,
            TypeParamInvariantAt::Unstatable,
            "p{p}: {:?}",
            answers[p].0
        );
    }
    assert!(
        !answers[11].0.is_empty(),
        "the refusal is not the absence of a premise"
    );
    // Owed nothing: nothing inside can carry an invariant, and nothing is granted.
    for p in 13..=17 {
        assert_eq!(answers[p].1, TypeParamInvariantAt::Nothing, "p{p}");
        assert!(answers[p].0.is_empty(), "p{p}: {:?}", answers[p].0);
    }
}
