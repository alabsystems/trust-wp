// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoder-side pins for the projected expiry pin (#prophecy-slots M5).
//!
//! The driver proves WHERE a caller-side borrow dies; this file pins what the
//! encoder does with that proof. Four properties, and the last two are the
//! teeth:
//!
//! 1. a guarded pin CLOSES the prophecy on the matching variant;
//! 2. the same pin is VACUOUS on the other variant — it never asserts anything
//!    about a term that denotes nothing;
//! 3. a non-carrier payload is REFUSED, not pinned — pinning `^` where no
//!    prophecy slot exists would silently assert `*p == e`, which is the
//!    take_first_mut false-accept shape one sort up;
//! 4. an unknown root is REFUSED — a pin on a symbol nothing else in the VC
//!    mentions is noise at best and a name collision at worst.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{ExprSort, FinalPinTarget, PinStep, ProjectedFinalPin, PureExpr};

use super::bindings::bind_projected_final_value;
use crate::encoder::{
    match_enc::{datatype_constructor_name, stdlib_option_datatype_for_payload},
    AYEncoder,
};

fn pin(target: FinalPinTarget, value: i64) -> ProjectedFinalPin {
    ProjectedFinalPin {
        target,
        value: PureExpr::Int(value),
        provenance: "m5-unit".to_string(),
    }
}

fn some_projection(root: &str) -> FinalPinTarget {
    FinalPinTarget::Projection {
        root: root.to_string(),
        root_sort: None,
        path: vec![PinStep::Variant {
            ctor: "Some".to_string(),
            field: 0,
        }],
    }
}

/// Declare `Option<__trust_wp_mutref::int>`, a carrier `r` with FREE
/// current/final/id, and bind `res == Some(r)`. Returns
/// `(payload_selector_term, res_term, datatype)`.
fn option_carrier_fixture(
    e: &mut AYEncoder,
    root: &str,
) -> (ay_dpll::api::Term, ay_dpll::api::Term) {
    let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let dt = stdlib_option_datatype_for_payload(mr.clone());
    e.ensure_datatype_declared(&dt);
    assert!(
        e.lookup_datatype_decl(&dt.name).is_some(),
        "fixture requires the Option<mutref> datatype to declare natively"
    );
    let dt_sort = Sort::Uninterpreted(dt.name.clone());

    let r = e.get_or_declare_var("r", mr.clone()).unwrap();
    let r_cur = e.get_or_declare_var("r_current", Sort::Int).unwrap();
    let r_fin = e.get_or_declare_var("r_final", Sort::Int).unwrap();
    let r_id = e.get_or_declare_var("r_id", Sort::Int).unwrap();
    e.bind_whole_mut_ref(&mr, &Sort::Int, r, r_cur, r_fin, r_id)
        .expect("whole mutref binding should encode");

    let res = e.get_or_declare_var(root, dt_sort).unwrap();
    let some_name = datatype_constructor_name(&dt, "Some");
    let built = e
        .solver_mut()
        .try_datatype_constructor(&dt, &some_name, &[r])
        .expect("Some(r) should construct");
    let (sel_name, sel_sort) =
        AYEncoder::constructor_payload_selector(&dt, "Some").expect("Some payload selector");
    let sel_sort = sel_sort.clone();
    let sel_name = sel_name.to_string();
    let payload = e
        .solver_mut()
        .try_datatype_selector(&sel_name, res, sel_sort)
        .expect("native selector over a carrier field should build");
    (payload, built)
}

/// ★PIN 1 (#prophecy-slots M5): the guarded pin closes `^payload == 43` on the
/// matching variant. This is the capability the whole milestone exists for —
/// before it, a caller could say nothing at all about the prophecy of a borrow
/// it received inside a payload.
#[test]
#[timeout(30000)]
fn guarded_pin_closes_the_prophecy_on_the_matching_variant() {
    let mut e = AYEncoder::new_all();
    let (payload, some_term) = option_carrier_fixture(&mut e, "res");
    let res = e.var_term("res").unwrap();
    e.assert_eq(res, some_term);

    let emitted = bind_projected_final_value(&mut e, &pin(some_projection("res"), 43))
        .expect("pin should encode");
    assert!(
        emitted,
        "a carrier payload with a declared datatype must pin"
    );

    let fin = e
        .mut_ref_component_projection(payload, true)
        .unwrap()
        .expect("payload must be MutRef-sorted");
    let forty_three = e.solver_mut().int_const(43);
    let eq = e.eq_term(fin, forty_three);
    let neq = e.solver_mut().not(eq);
    e.assert_term(neq);
    assert!(
        matches!(e.check_sat(), SolveResult::Unsat(_)),
        "the guarded pin must force ^payload == 43 when the carrier IS Some"
    );
}

/// ★PIN 2 — VACUITY: with the receiver on the OTHER variant the pin constrains
/// nothing. An unguarded pin here would be a fact about a term that denotes
/// nothing (the blueprint's `optmut_none_branch_pin` shape) and, being
/// consistent, would be invisible to every vacuity counter.
#[test]
#[timeout(30000)]
fn guarded_pin_is_vacuous_on_the_other_variant() {
    let mut e = AYEncoder::new_all();
    let (payload, _some_term) = option_carrier_fixture(&mut e, "res");

    // Pin the SOME payload, then force the receiver to be NONE.
    let emitted = bind_projected_final_value(&mut e, &pin(some_projection("res"), 43))
        .expect("pin should encode");
    assert!(emitted);

    let res = e.var_term("res").unwrap();
    let dt_name = match e.solver().get_sort(res) {
        Sort::Uninterpreted(name) => name,
        other => panic!("carrier Option must be an uninterpreted datatype sort, got {other:?}"),
    };
    let dt = e
        .lookup_datatype_decl(&dt_name)
        .cloned()
        .expect("declared datatype");
    let none_name =
        crate::encoder::match_enc::short_constructor_name(&datatype_constructor_name(&dt, "None"))
            .to_string();
    let none_tester = e
        .solver_mut()
        .try_datatype_tester(&none_name, res)
        .expect("None tester should build");
    e.assert_term(none_tester);

    // `^payload == 43` must NOT be derivable: its negation stays satisfiable.
    let fin = e
        .mut_ref_component_projection(payload, true)
        .unwrap()
        .expect("payload must be MutRef-sorted");
    let forty_three = e.solver_mut().int_const(43);
    let eq = e.eq_term(fin, forty_three);
    let neq = e.solver_mut().not(eq);
    e.assert_term(neq);
    assert!(
        !matches!(e.check_sat(), SolveResult::Unsat(_)),
        "★the pin must be VACUOUS on the None branch — deriving ^payload == 43 \
         there would be a fabricated premise no vacuity counter can see"
    );
}

/// ★TEETH 1 — the carrier requirement. `Option<i32>` has no prophecy slot, so
/// `^payload` and `*payload` would be the same symbol and the "pin" would
/// silently assert the CURRENT value. Refuse instead.
#[test]
#[timeout(30000)]
fn non_carrier_payload_is_refused() {
    let mut e = AYEncoder::new_all();
    let dt = stdlib_option_datatype_for_payload(Sort::Int);
    e.ensure_datatype_declared(&dt);
    let dt_sort = Sort::Uninterpreted(dt.name.clone());
    e.get_or_declare_var("res", dt_sort).unwrap();

    let emitted = bind_projected_final_value(&mut e, &pin(some_projection("res"), 43))
        .expect("refusal is not an error");
    assert!(
        !emitted,
        "★an Int payload carries no prophecy slot — pinning `^` on it would \
         assert the CURRENT value, which is the take_first_mut false accept"
    );
}

/// ★TEETH 2 — an unknown root. A pin on a name the VC never mentions
/// constrains a fresh symbol: useless at best, a collision at worst.
#[test]
#[timeout(30000)]
fn unknown_root_is_refused() {
    let mut e = AYEncoder::new_all();
    let emitted = bind_projected_final_value(&mut e, &pin(some_projection("nowhere"), 43))
        .expect("refusal is not an error");
    assert!(!emitted, "an undeclared root must not be pinned");
}

/// ★TEETH 3 — a variant step on a receiver whose sort is not a declared
/// datatype has no tester, and an UNGUARDED enum-payload pin is exactly the
/// shape the vacuity test above exists to forbid. Refuse.
#[test]
#[timeout(30000)]
fn variant_step_without_a_datatype_receiver_is_refused() {
    let mut e = AYEncoder::new_all();
    e.get_or_declare_var("res", Sort::Int).unwrap();
    let emitted = bind_projected_final_value(&mut e, &pin(some_projection("res"), 43))
        .expect("refusal is not an error");
    assert!(
        !emitted,
        "no declared datatype means no tester means no guarded pin"
    );
}

/// The `Local` lane: a carrier addressed by its own name pins unguarded, and a
/// non-carrier local is refused by the same rule as the projected lane.
#[test]
#[timeout(30000)]
fn local_pin_closes_for_a_carrier_and_refuses_a_non_carrier() {
    let mut e = AYEncoder::new_all();
    let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let p = e.get_or_declare_var("p", mr.clone()).unwrap();
    let p_cur = e.get_or_declare_var("p_current", Sort::Int).unwrap();
    let p_fin = e.get_or_declare_var("p_final", Sort::Int).unwrap();
    let p_id = e.get_or_declare_var("p_id", Sort::Int).unwrap();
    e.bind_whole_mut_ref(&mr, &Sort::Int, p, p_cur, p_fin, p_id)
        .unwrap();

    let emitted =
        bind_projected_final_value(&mut e, &pin(FinalPinTarget::Local("p".to_string()), 7))
            .expect("pin should encode");
    assert!(emitted, "a MutRef-sorted local must pin");

    let seven = e.solver_mut().int_const(7);
    let eq = e.eq_term(p_fin, seven);
    let neq = e.solver_mut().not(eq);
    e.assert_term(neq);
    assert!(
        matches!(e.check_sat(), SolveResult::Unsat(_)),
        "^p == 7 must be forced by the local pin"
    );

    // A plain Int local has no prophecy slot.
    let mut e2 = AYEncoder::new_all();
    e2.get_or_declare_var("q", Sort::Int).unwrap();
    let emitted2 =
        bind_projected_final_value(&mut e2, &pin(FinalPinTarget::Local("q".to_string()), 7))
            .expect("refusal is not an error");
    assert!(!emitted2, "an Int local must be refused, never pinned");
}
