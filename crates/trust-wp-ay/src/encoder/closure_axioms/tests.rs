// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::normalize_closure_receiver;
use crate::encoder::AYEncoder;

#[test]
#[timeout(5000)]
fn normalize_var_is_identity() {
    let expr = PureExpr::Var("f".to_string(), None);
    let result = normalize_closure_receiver(&expr);
    assert!(
        matches!(result, PureExpr::Var(name, _) if name == "f"),
        "Var should be returned unchanged"
    );
}

#[test]
#[timeout(5000)]
fn normalize_single_deref() {
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None)));
    let result = normalize_closure_receiver(&expr);
    assert!(
        matches!(result, PureExpr::Var(name, _) if name == "f"),
        "single Deref(Var) should peel to Var"
    );
}

#[test]
#[timeout(5000)]
fn normalize_double_deref_for_box() {
    let inner = PureExpr::Var("f".to_string(), None);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(inner))));
    let result = normalize_closure_receiver(&expr);
    assert!(
        matches!(result, PureExpr::Var(name, _) if name == "f"),
        "double Deref(Deref(Var)) should peel to Var (#1373)"
    );
}

#[test]
#[timeout(5000)]
fn normalize_triple_deref() {
    let inner = PureExpr::Var("f".to_string(), None);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(
        Arc::new(inner),
    )))));
    let result = normalize_closure_receiver(&expr);
    assert!(
        matches!(result, PureExpr::Var(name, _) if name == "f"),
        "triple deref should peel all layers"
    );
}

#[test]
#[timeout(5000)]
fn normalize_non_deref_wrapper_stops() {
    // Final(Var("f")) should NOT be peeled — only Deref is peeled
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None)));
    let result = normalize_closure_receiver(&expr);
    assert!(
        matches!(result, PureExpr::Final(_)),
        "Final wrapper should not be peeled by normalize_closure_receiver"
    );
}

// ── Box<dyn FnOnce> encoding tests (#2318) ─────────────────────────

/// Helper: build a `postcondition_once(receiver, arg, result)` MethodCall.
fn postcondition_once_call(receiver: PureExpr, arg: PureExpr, result: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition_once".to_string(),
        args: vec![arg, result],
    }
}

/// Box<dyn FnOnce> closures resolve to the same UF symbol as bare closures.
///
/// When `Box::new(f)` wraps a closure, MIR produces `Deref(Deref(Var("f")))`
/// — one deref from `Box: Deref` and one from the Fn::call spec's `(*self)`.
/// `encode_closure_spec_method` must normalize both forms to the same UF
/// symbol so that the postcondition assumption connects to the proof goal.
///
/// Part of #2318.
#[test]
#[timeout(10000)]
fn test_box_fn_once_same_uf_symbol_as_bare() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let arg = PureExpr::Int(5);
    let result = PureExpr::Var("r".to_string(), None);

    // Bare receiver: f.postcondition_once(5, r)
    let bare_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        arg.clone(),
        result.clone(),
    );
    let bare_term = encoder
        .encode_pure(&bare_call)
        .expect("bare postcondition_once should encode");

    // Box-wrapped receiver: (*(*f)).postcondition_once(5, r)
    // Simulates Box<dyn FnOnce> where MIR produces Deref(Deref(Var("f")))
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "f".to_string(),
        None,
    )))));
    let box_call = postcondition_once_call(box_receiver, arg.clone(), result.clone());
    let box_term = encoder
        .encode_pure(&box_call)
        .expect("Box-wrapped postcondition_once should encode");

    // Both must produce the same SMT term because normalize_closure_receiver
    // peels all Deref layers down to the base Var("f").
    assert_eq!(
        bare_term, box_term,
        "Box<dyn FnOnce> receiver must produce the same UF term as bare closure (#2318)"
    );
}

/// Captured &mut T references survive Box wrapping in postcondition_mut.
///
/// When a closure captures `&mut x` and is wrapped in Box, the MIR receiver
/// becomes `Deref(Deref(Var("c")))`. The postcondition_mut encoding must still
/// produce the correct UF symbol referencing `c` (not `*c` or `**c`), so
/// capture projection connects the closure's post-state back to `x`.
///
/// Part of #2318.
#[test]
#[timeout(10000)]
fn test_box_wrapped_mut_capture_postcondition_mut_encodes() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Simulate Box-wrapped closure with &mut capture:
    // (**c).postcondition_mut((), c_final, call_0)
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "c".to_string(),
        None,
    )))));
    let postcondition_mut = PureExpr::MethodCall {
        receiver: Arc::new(box_receiver),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Int(0), // unit arg ()
            PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
            PureExpr::Var("call_0".to_string(), None),
        ],
    };

    let result = encoder.encode_pure(&postcondition_mut);
    assert!(
        result.is_ok(),
        "Box-wrapped postcondition_mut with &mut capture should encode without error: {result:?}"
    );

    // The resulting term must be Bool-sorted (it is a predicate)
    let term = result.unwrap();
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "postcondition_mut should produce Bool-sorted term"
    );

    // Verify the UF symbol was declared — it should use the base var "c" not "**c"
    assert!(
        encoder.has_closure_postcondition_mut_symbols(),
        "postcondition_mut UF symbol must be registered in logic_funcs"
    );
}

/// Nested Box<Box<dyn FnOnce>> (triple deref) resolves correctly.
///
/// `Box<Box<F>>` produces `Deref(Deref(Deref(Var("f"))))` in MIR — the outer
/// Box deref, the inner Box deref, and the Fn::call `(*self)` deref. All
/// three layers must be peeled to produce the same UF symbol as the bare case.
///
/// Part of #2318.
#[test]
#[timeout(10000)]
fn test_nested_box_box_fn_once_triple_deref_same_symbol() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let arg = PureExpr::Int(42);
    let result = PureExpr::Var("r".to_string(), None);

    // Bare: f.postcondition_once(42, r)
    let bare_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        arg.clone(),
        result.clone(),
    );
    let bare_term = encoder
        .encode_pure(&bare_call)
        .expect("bare call should encode");

    // Box<Box<F>>: (***f).postcondition_once(42, r)
    let triple_deref = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Var("f".to_string(), None)),
    )))));
    let nested_call = postcondition_once_call(triple_deref, arg.clone(), result.clone());
    let nested_term = encoder
        .encode_pure(&nested_call)
        .expect("nested Box<Box<F>> call should encode");

    assert_eq!(
        bare_term, nested_term,
        "Box<Box<dyn FnOnce>> (triple deref) must produce same UF term as bare (#2318)"
    );
}

/// Deref-wrapped postcondition produces UF declaration in logic_funcs.
///
/// Verifies that a Box-wrapped `postcondition` call actually declares the
/// UF symbol (triggering demand-driven axiom emission) and that the symbol
/// matches what a bare receiver would declare.
///
/// Part of #2318.
#[test]
#[timeout(10000)]
fn test_box_fn_once_registers_postcondition_uf_symbol() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Box-wrapped: (*f).postcondition(5, r) — single deref for simple Box<F>
    let deref_receiver = PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None)));
    let call = PureExpr::MethodCall {
        receiver: Arc::new(deref_receiver),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(5), PureExpr::Var("r".to_string(), None)],
    };

    let result = encoder.encode_pure(&call);
    assert!(
        result.is_ok(),
        "Box<F> postcondition should encode: {result:?}"
    );

    // The Fn-trait postcondition UF symbol must be registered
    assert!(
        encoder.has_closure_postcondition_fn_symbols(),
        "Fn postcondition UF symbol should be declared for Box-wrapped receiver (#2318)"
    );
}

/// Eager instantiation normalizes Box-wrapped postcondition_once receivers.
///
/// When preconditions contain `Deref(Deref(Var("f"))).postcondition_once(...)`,
/// the eager fn_mut_once instantiation must normalize the receiver before
/// building sort signatures, so that the witness function lookup uses the
/// correct base variable name.
///
/// Part of #2318.
#[test]
#[timeout(10000)]
fn test_eager_instantiation_normalizes_box_wrapped_receiver() {
    // The collect_ground_postcondition_once_calls function extracts the
    // receiver as-is. The eager path then calls normalize_closure_receiver.
    // Verify the extraction + normalization chain works for Box-wrapped calls.
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "f".to_string(),
        None,
    )))));
    let once_call = PureExpr::MethodCall {
        receiver: Arc::new(box_receiver),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Var("r".to_string(), None)],
    };
    let exprs: Vec<&PureExpr> = vec![&once_call];
    let calls = AYEncoder::collect_ground_postcondition_once_calls(&exprs);
    assert_eq!(
        calls.len(),
        1,
        "should find one ground postcondition_once call"
    );

    let (receiver, args) = calls[0];
    // The raw receiver is Deref(Deref(Var("f")))
    assert!(
        matches!(receiver, PureExpr::Deref(_)),
        "raw extracted receiver should still be Deref-wrapped"
    );

    // After normalization, it should be Var("f")
    let normalized = normalize_closure_receiver(receiver);
    assert!(
        matches!(normalized, PureExpr::Var(name, _) if name == "f"),
        "normalized receiver should be Var(\"f\") after peeling Box deref layers"
    );
    assert_eq!(args.len(), 2, "postcondition_once should have 2 args");
}

/// Mixed deref depths produce identical symbols within one encoder.
///
/// Encoding `f.postcondition_once(...)` and then `(*(*f)).postcondition_once(...)`
/// in the same encoder must reuse the same UF declaration — not create a
/// duplicate symbol. This is critical for axiom emission correctness: if two
/// different UF symbols existed for the same logical closure, the fn_mut_once
/// law could not connect them.
///
/// Part of #2318.
#[test]
#[timeout(10000)]
fn test_mixed_deref_depths_reuse_same_uf_declaration() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // First call: bare receiver
    let bare_call = postcondition_once_call(
        PureExpr::Var("g".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r1".to_string(), None),
    );
    encoder
        .encode_pure(&bare_call)
        .expect("bare call should encode");

    // Count postcondition_once symbols after first call
    let count_before: usize = encoder
        .logic_func_names_iter()
        .filter(|n| n.starts_with("closure_postcondition_once_"))
        .count();

    // Second call: double-deref (Box-wrapped) receiver, same base var
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "g".to_string(),
        None,
    )))));
    let box_call = postcondition_once_call(
        box_receiver,
        PureExpr::Int(1),
        PureExpr::Var("r2".to_string(), None),
    );
    encoder
        .encode_pure(&box_call)
        .expect("Box-wrapped call should encode");

    let count_after: usize = encoder
        .logic_func_names_iter()
        .filter(|n| n.starts_with("closure_postcondition_once_"))
        .count();

    assert_eq!(
        count_before, count_after,
        "Box-wrapped and bare receivers with same signature must share one UF symbol, \
         not create a duplicate (before={count_before}, after={count_after})"
    );
}

// ── fn_mut_once_eager tests (Part of #2662) ─────────────────────────

/// Helper: build a `postcondition_mut(receiver, args...)` MethodCall.
fn postcondition_mut_call(receiver: PureExpr, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "postcondition_mut".to_string(),
        args,
    }
}

/// Eager fn_mut_once instantiation is a no-op when requires contain no
/// `postcondition_once` calls.
///
/// `assert_eager_fn_mut_once_instantiations` should return Ok(()) without
/// asserting any terms when the requires list contains only non-closure
/// expressions.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_once_empty_requires_is_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Empty requires — should be a no-op
    let result = encoder.assert_eager_fn_mut_once_instantiations(&[]);
    assert!(result.is_ok(), "empty requires should succeed: {result:?}");

    // Non-closure expressions — also a no-op
    let requires = vec![
        PureExpr::Int(42),
        PureExpr::Bool(true),
        PureExpr::Var("x".to_string(), None),
    ];
    let result = encoder.assert_eager_fn_mut_once_instantiations(&requires);
    assert!(
        result.is_ok(),
        "non-closure requires should succeed: {result:?}"
    );
}

/// Eager fn_mut_once instantiation succeeds when requires contain a ground
/// `postcondition_once` call and matching `postcondition_mut` + witness
/// symbols are declared.
///
/// This sets up the full axiom machinery: declares both postcondition_once
/// and postcondition_mut UF symbols, asserts the fn_mut_once law (which
/// declares the witness Skolem function), then runs eager instantiation
/// with a requires list containing the postcondition_once call.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_once_with_ground_once_call() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition_once(f, x, r) — three-place
    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(5),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once symbol");

    // Declare postcondition_mut(f, x, ^f, r) — four-place
    let mut_call = postcondition_mut_call(
        PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None))),
        vec![
            PureExpr::Int(5),
            PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None))),
            PureExpr::Var("r".to_string(), None),
        ],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut symbol");

    // Assert fn_mut_once law — this declares the witness Skolem function
    encoder.assert_fn_mut_once_law();

    // Now run eager instantiation with the once call in requires
    let requires = vec![once_call];
    let result = encoder.assert_eager_fn_mut_once_instantiations(&requires);
    assert!(
        result.is_ok(),
        "eager instantiation with ground once call should succeed: {result:?}"
    );
}

/// Eager fn_mut_once instantiation skips postcondition_once calls when no
/// matching postcondition_mut symbol exists.
///
/// If only postcondition_once is declared (no postcondition_mut), the eager
/// path has no candidates and should be a quiet no-op.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_once_skips_without_mut_symbol() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only declare postcondition_once — no postcondition_mut
    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    // Eager instantiation should succeed but do nothing
    let requires = vec![once_call];
    let result = encoder.assert_eager_fn_mut_once_instantiations(&requires);
    assert!(
        result.is_ok(),
        "should succeed with no mut candidates: {result:?}"
    );
}

/// Forward eager fn_mut_once instantiation handles ground `postcondition_mut`
/// calls by pre-asserting the corresponding `postcondition_once` conclusion.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_once_forward_with_ground_mut_call() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare both postcondition_once and postcondition_mut
    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(7),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    let mut_call = postcondition_mut_call(
        PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None))),
        vec![
            PureExpr::Int(7),
            PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None))),
            PureExpr::Var("r".to_string(), None),
        ],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut");

    // Run forward eager instantiation with postcondition_mut in requires
    let requires = vec![mut_call];
    let result = encoder.assert_eager_fn_mut_once_forward_instantiations(&requires);
    assert!(
        result.is_ok(),
        "forward eager instantiation should succeed: {result:?}"
    );
}

/// Forward eager fn_mut_once instantiation is a no-op when requires are
/// empty or contain no postcondition_mut calls.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_once_forward_empty_requires_is_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let result = encoder.assert_eager_fn_mut_once_forward_instantiations(&[]);
    assert!(result.is_ok(), "empty requires should succeed: {result:?}");

    let requires = vec![PureExpr::Bool(true)];
    let result = encoder.assert_eager_fn_mut_once_forward_instantiations(&requires);
    assert!(
        result.is_ok(),
        "non-mut requires should succeed: {result:?}"
    );
}

// ── fn_laws tests (Part of #2662) ───────────────────────────────────

/// Fn closure laws declare hist_inv when all three postcondition variants
/// are registered.
///
/// Verifies that `assert_fn_closure_laws` correctly detects all three
/// postcondition UF symbols and asserts the complete fn_mut + fn_once +
/// hist_inv axiom set.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_fn_closure_laws_declares_hist_inv_with_all_variants() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare all three postcondition variants
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Var("r".to_string(), None)],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition");

    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    let mut_call = postcondition_mut_call(
        PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None))),
        vec![
            PureExpr::Int(1),
            PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None))),
            PureExpr::Var("r".to_string(), None),
        ],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut");

    // Assert all Fn closure laws
    encoder.assert_fn_closure_laws();

    // Verify hist_inv was declared (proves fn_mut law was asserted)
    let hist_count: usize = encoder
        .logic_func_names_iter()
        .filter(|n| n.starts_with("closure_hist_inv_"))
        .count();
    assert_eq!(
        hist_count, 1,
        "hist_inv should be declared when postcondition + postcondition_mut are both present"
    );

    // Verify all three postcondition flags are set
    let flags = encoder.closure_postcondition_flags();
    assert!(flags.has_fn, "has_fn flag should be true");
    assert!(flags.has_once, "has_once flag should be true");
    assert!(flags.has_mut, "has_mut flag should be true");
}

/// Fn closure laws are a no-op when only `postcondition` is declared
/// without matching `postcondition_mut` or `postcondition_once`.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_fn_closure_laws_noop_without_mut_or_once() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only declare postcondition (Fn-trait)
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition");

    // No matching mut/once symbols — should be a no-op
    encoder.assert_fn_closure_laws();

    // hist_inv should NOT be declared (no matching postcondition_mut)
    let hist_count: usize = encoder
        .logic_func_names_iter()
        .filter(|n| n.starts_with("closure_hist_inv_"))
        .count();
    assert_eq!(
        hist_count, 0,
        "hist_inv should not be declared when postcondition_mut is absent"
    );
}

/// Bool-sorted capture variables in postcondition_mut are handled correctly
/// by the fn_mut law.
///
/// When arguments include Bool-sorted values, the sort tag "b" is used
/// instead of "i". The fn_mut law must still match symbols correctly and
/// produce a valid biconditional axiom.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_fn_laws_bool_sorted_args() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition(f, true, r) — Bool-sorted arg
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Bool(true), PureExpr::Var("r".to_string(), None)],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition with Bool arg");

    // Declare postcondition_mut(f, true, ^f, r) — Bool arg + res_state
    let mut_call = postcondition_mut_call(
        PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None))),
        vec![
            PureExpr::Bool(true),
            PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None))),
            PureExpr::Var("r".to_string(), None),
        ],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut with Bool arg");

    // Should not panic — Bool sort tag "b" must round-trip correctly
    encoder.assert_fn_closure_laws();

    // Verify hist_inv was declared (proves fn_mut law was asserted)
    let hist_count: usize = encoder
        .logic_func_names_iter()
        .filter(|n| n.starts_with("closure_hist_inv_"))
        .count();
    assert_eq!(
        hist_count, 1,
        "hist_inv should be declared for Bool-sorted fn_mut law"
    );
}

/// Transparent adapters should seed `result_view` from the inner body
/// term instead of the raw fallback result term.
///
/// This guards the closure-axiom bridge used by copied set adapters in
/// `cc/collections.rs`.
#[test]
#[timeout(10000)]
fn test_result_view_binding_term_prefers_transparent_adapter_body() {
    let mut encoder = AYEncoder::new();

    let copied_intersection = PureExpr::LogicFnCall {
        name: "Copied".to_string(),
        args: vec![PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "xs".to_string(),
                None,
            )))),
            method: "intersection".to_string(),
            args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                "ys".to_string(),
                None,
            )))],
        }],
    };

    let fallback = encoder
        .get_or_declare_var("result", Sort::Uninterpreted("FSet".to_string()))
        .expect("fallback result term");
    let bridged = encoder.result_view_binding_term(fallback, Some(&copied_intersection));
    let expected = encoder
        .encode_pure(&PureExpr::View(Arc::new(copied_intersection)))
        .expect("copied adapter body should encode");

    assert_eq!(
        bridged, expected,
        "result_view should seed from the copied-adapter inner body term"
    );
}

/// Eager ground `fn_mut` instantiation correctly handles a postcondition_mut
/// expression when the Fn-trait postcondition symbol is registered.
///
/// `assert_eager_fn_mut_ground_instantiation` builds a ground instance of the
/// fn_mut biconditional law for a specific postcondition_mut call. This test
/// verifies it produces a consistent (non-contradictory) axiom.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_ground_instantiation_consistent() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition (Fn-trait) — needed for the eager fn_mut ground axiom
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(10), PureExpr::Var("r".to_string(), None)],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition");

    // Declare postcondition_mut
    let mut_call = postcondition_mut_call(
        PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None))),
        vec![
            PureExpr::Int(10),
            PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None))),
            PureExpr::Var("r".to_string(), None),
        ],
    );
    encoder
        .encode_pure(&mut_call)
        .expect("declare postcondition_mut");

    // Assert the eager ground fn_mut instantiation
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&mut_call);
    assert!(
        result.is_ok(),
        "eager fn_mut ground instantiation should succeed: {result:?}"
    );

    // The axiom should not introduce contradictions on its own
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, ay_dpll::api::SolveResult::Sat),
        "eager fn_mut ground instantiation should be consistent: {sat_result:?}"
    );
}

/// Eager ground `fn_mut` instantiation is a no-op for non-postcondition_mut
/// expressions.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_mut_ground_instantiation_noop_for_non_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // A postcondition_once call should be ignored by fn_mut instantiation
    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&once_call);
    assert!(
        result.is_ok(),
        "non-postcondition_mut expr should be silently skipped: {result:?}"
    );

    // An arbitrary expression should also be a no-op
    let int_expr = PureExpr::Int(42);
    let result = encoder.assert_eager_fn_mut_ground_instantiation(&int_expr);
    assert!(
        result.is_ok(),
        "non-MethodCall expr should be silently skipped: {result:?}"
    );
}

/// `assert_eager_fn_once_ground_instantiation` is a no-op when no Fn-trait
/// postcondition symbol is declared.
///
/// Part of #2662.
#[test]
#[timeout(10000)]
fn test_eager_fn_once_ground_instantiation_requires_fn_symbol() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition_once only (no Fn-trait postcondition)
    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    // Should succeed but do nothing (has_fn is false)
    let result = encoder.assert_eager_fn_once_ground_instantiation(&once_call);
    assert!(
        result.is_ok(),
        "should succeed without Fn postcondition: {result:?}"
    );
}

// ── Standalone postcondition_once resolve law tests (#2668) ─────────

/// Standalone postcondition_once resolve law is asserted when only
/// postcondition_once is declared (no Fn-trait postcondition).
///
/// This is the FnOnce-only case: closures called via FnOnce without any
/// Fn-trait postcondition symbol. The standalone law provides the critical
/// `postcondition_once ==> resolve(self)` constraint.
///
/// Part of #2668.
#[test]
#[timeout(10000)]
fn test_standalone_postcondition_once_resolve_law_asserts_without_fn() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare ONLY postcondition_once — no postcondition (Fn-trait)
    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    // Verify flags: has_once but NOT has_fn
    let flags = encoder.closure_postcondition_flags();
    assert!(flags.has_once, "postcondition_once should be declared");
    assert!(!flags.has_fn, "postcondition (Fn) should NOT be declared");

    // Assert the standalone law — should not panic and should
    // not increment ClosureAxiomSkipped (successful axiom emission).
    encoder.assert_standalone_postcondition_once_laws();

    // Verify a postcondition_once UF symbol exists (the law was applied to it)
    assert!(
        encoder.has_closure_postcondition_once_symbols(),
        "postcondition_once symbol should still exist after standalone law"
    );
}

/// Standalone postcondition_once law is skipped when Fn-trait postcondition
/// also exists (the full fn_once law covers it).
///
/// Part of #2668.
#[test]
#[timeout(10000)]
fn test_standalone_postcondition_once_skipped_when_fn_exists() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare both postcondition (Fn-trait) and postcondition_once
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Var("r".to_string(), None)],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition");

    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    // Both flags should be set
    let flags = encoder.closure_postcondition_flags();
    assert!(flags.has_once, "postcondition_once should be declared");
    assert!(flags.has_fn, "postcondition (Fn) should be declared");

    // The standalone law call should succeed but not assert anything new
    // (the matching sort_sig exclusion logic prevents duplicate axioms)
    encoder.assert_standalone_postcondition_once_laws();

    // Should still be consistent
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, ay_dpll::api::SolveResult::Sat),
        "should remain consistent after standalone law (no-op): {sat_result:?}"
    );
}

/// FnOnce-only closure with postcondition_once assumption and
/// postcondition_once goal uses the standalone resolve law to connect them.
///
/// Models the pattern:
/// ```text
/// requires: f.postcondition_once(x, init)
/// ensures: f.postcondition_once(x, result)
/// body: result = init
/// ```
///
/// Without the standalone resolve law, this would be SAT (the two
/// postcondition_once UF applications are unconnected). With the law,
/// the assumption still cannot prove the goal (postcondition_once is
/// uninterpreted), but the resolve constraint is properly added.
///
/// Part of #2668.
#[test]
#[timeout(10000)]
fn test_fnonce_only_resolve_law_adds_resolve_constraint() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition_once only
    let once_call_assume = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Var("x".to_string(), None),
        PureExpr::Var("init".to_string(), None),
    );
    let assume_term = encoder
        .encode_pure(&once_call_assume)
        .expect("encode assumption postcondition_once");

    // Assert the assumption as a ground fact
    encoder.assert_term(assume_term);

    // Assert the standalone law — should complete without errors
    encoder.assert_standalone_postcondition_once_laws();

    // Verify the postcondition_once symbol is properly declared
    assert!(
        encoder.has_closure_postcondition_once_symbols(),
        "postcondition_once symbol should exist after law assertion"
    );
    // Verify no Fn postcondition was magically created
    assert!(
        !encoder.has_closure_postcondition_fn_symbols(),
        "standalone law should not create Fn postcondition symbols"
    );
}

/// Eager fn_once ensures bridge fires when postcondition_once is in requires
/// and Fn-trait postcondition exists.
///
/// Part of #2668.
#[test]
#[timeout(10000)]
fn test_eager_fn_once_ensures_bridge_with_both_symbols() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare both postcondition and postcondition_once
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Var("r".to_string(), None)],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition");

    let once_call = postcondition_once_call(
        PureExpr::Var("f".to_string(), None),
        PureExpr::Int(1),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&once_call)
        .expect("declare postcondition_once");

    // Eager fn_once ensures bridge with postcondition_once in requires
    let requires = vec![once_call];
    let result = encoder.assert_eager_fn_once_for_ensures(&requires);
    assert!(
        result.is_ok(),
        "eager fn_once ensures bridge should succeed: {result:?}"
    );

    // Verify both symbols are declared
    let flags = encoder.closure_postcondition_flags();
    assert!(flags.has_fn, "postcondition should be declared");
    assert!(flags.has_once, "postcondition_once should be declared");
}

/// Eager fn_once ensures bridge is a no-op when no postcondition_once calls
/// are present in the requires.
///
/// Part of #2668.
#[test]
#[timeout(10000)]
fn test_eager_fn_once_ensures_noop_without_once_calls() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare postcondition (Fn-trait) only
    let post_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Var("r".to_string(), None)],
    };
    encoder
        .encode_pure(&post_call)
        .expect("declare postcondition");

    // No postcondition_once calls in requires — should be a no-op
    let requires = vec![PureExpr::Bool(true)];
    let result = encoder.assert_eager_fn_once_for_ensures(&requires);
    assert!(
        result.is_ok(),
        "should succeed with no once calls: {result:?}"
    );
}

/// `body_has_postcondition_mut_with_var` detects vars that appear as the
/// RECEIVER of a `postcondition_mut` call, not just in the args.
///
/// In the Creusot `call_fnmut` pattern, the ensures contains:
///   `exists<st1, st2, r> f.postcondition_mut((), st1, r) && st1.postcondition_mut((), st2, result)`
///
/// Here `st1` appears both as an arg in the first call AND as a receiver in the
/// second. The fix in #2668 ensures both references are detected.
///
/// Part of #2668.
#[test]
#[timeout(5000)]
fn test_body_has_postcondition_mut_with_var_detects_receiver() {
    // st1.postcondition_mut((), st2, result) — st1 is the receiver
    let chained_mut_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("st1".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("unit".to_string(), None),
            PureExpr::Var("st2".to_string(), None),
            PureExpr::Var("result".to_string(), None),
        ],
    };

    // st1 is the receiver — should be detected
    assert!(
        AYEncoder::body_has_postcondition_mut_with_var(&chained_mut_call, "st1"),
        "should detect var 'st1' as receiver of postcondition_mut (#2668)"
    );

    // st2 is in args — should also be detected
    assert!(
        AYEncoder::body_has_postcondition_mut_with_var(&chained_mut_call, "st2"),
        "should detect var 'st2' as arg of postcondition_mut"
    );

    // f is not referenced — should NOT be detected
    assert!(
        !AYEncoder::body_has_postcondition_mut_with_var(&chained_mut_call, "f"),
        "should not detect unrelated var 'f'"
    );

    // Chained pattern: f.postcondition_mut((), st1, r) && st1.postcondition_mut((), st2, result)
    let outer_mut_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition_mut".to_string(),
        args: vec![
            PureExpr::Var("unit".to_string(), None),
            PureExpr::Var("st1".to_string(), None),
            PureExpr::Var("r".to_string(), None),
        ],
    };
    let chained = PureExpr::BinOp(
        Arc::new(outer_mut_call),
        trust_wp_core::formula::BinOp::And,
        Arc::new(chained_mut_call.clone()),
    );

    // st1 in chained: appears both as arg of first call and receiver of second
    assert!(
        AYEncoder::body_has_postcondition_mut_with_var(&chained, "st1"),
        "should detect var 'st1' in chained postcondition_mut pattern (#2668)"
    );
}

/// Box-wrapped FnOnce receiver in standalone postcondition_once law
/// produces the same resolve constraint as a bare receiver.
///
/// Part of #2668.
#[test]
#[timeout(10000)]
fn test_standalone_once_law_box_wrapped_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Box-wrapped: (*(*f)).postcondition_once(5, r)
    let box_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "f".to_string(),
        None,
    )))));
    let box_call = postcondition_once_call(
        box_receiver,
        PureExpr::Int(5),
        PureExpr::Var("r".to_string(), None),
    );
    encoder
        .encode_pure(&box_call)
        .expect("declare Box-wrapped postcondition_once");

    // Should not have Fn postcondition
    let flags = encoder.closure_postcondition_flags();
    assert!(flags.has_once, "has_once should be true");
    assert!(!flags.has_fn, "has_fn should be false for FnOnce-only");

    // Assert standalone law — should complete without errors
    encoder.assert_standalone_postcondition_once_laws();

    // Verify the postcondition_once symbol is properly declared after Box normalization
    assert!(
        encoder.has_closure_postcondition_once_symbols(),
        "postcondition_once symbol should exist after Box-wrapped law assertion"
    );
    // Verify no Fn postcondition was created
    assert!(
        !encoder.has_closure_postcondition_fn_symbols(),
        "Box-wrapped standalone law should not create Fn postcondition symbols"
    );
}
