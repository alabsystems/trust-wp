// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PredCell and PermCell encoding path tests.
//!
//! Covers the view-lowering, sort inference, method dispatch, and
//! Mapping-based predicate application paths for PredCell and PermCell
//! types. Part of #2316 (PredCell/PermCell compat recovery).

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

use super::helpers::*;
use crate::encoder::AYEncoder;

// ── PredCell view produces Mapping sort ──

#[test]
#[timeout(30000)]
fn test_predcell_view_is_mapping_sort() {
    // View(Var("cell", PredCell)) should produce a term with Mapping sort,
    // since PredCell<T>.view() : Mapping<T, bool>.
    let mut encoder = AYEncoder::new();
    let predcell_id = intern_sort_name("PredCell");
    let cell_var = var_with_sort("cell", ExprSort::Datatype(predcell_id));
    let cell_view = view(cell_var);

    let result = encoder.encode_pure(&cell_view);
    assert!(result.is_ok(), "View(PredCell) should encode successfully");
}

#[test]
#[timeout(30000)]
fn test_predcell_view_through_ref() {
    // View(Deref(Var("cell", Ref(PredCell)))) should also work.
    let mut encoder = AYEncoder::new();
    let predcell_id = intern_sort_name("PredCell");
    let ref_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(predcell_id)));
    let cell_var = var_with_sort("cell", ref_sort);
    let cell_view = view(deref(cell_var));

    let result = encoder.encode_pure(&cell_view);
    assert!(
        result.is_ok(),
        "View(Deref(Var(cell, Ref(PredCell)))) should encode: {:?}",
        result.err()
    );
}

// ── PredCell method dispatch: get ──
// NOTE: PredCell::get(&self) -> T is a zero-arg method. In spec context
// the postcondition is `self@[result]`, not a direct `.get()` call.
// Direct `.get()` encoding panics at collection_methods.rs:220 because
// the "get" token routes through the FMap dispatch path which expects
// args[0]. The actual contract uses View+index, tested below.

// ── PredCellSlice indexing returns PredCell sort ──

#[test]
#[timeout(30000)]
fn test_predcell_slice_index_returns_predcell_sort() {
    // For a PredCellSlice receiver, index(i) should be inferred as PredCell sort.
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));
    let index_expr = method_call(receiver, "index", vec![int(0)]);

    let mut encoder = AYEncoder::new();
    let sort = encoder.infer_expr_sort_with_context(&index_expr, None);
    assert_eq!(
        sort,
        Sort::Uninterpreted("PredCell".to_string()),
        "PredCellSlice.index(i) should infer PredCell sort"
    );
}

// ── PredCellSlice index view is Mapping ──

#[test]
#[timeout(30000)]
fn test_predcell_slice_index_view_is_mapping_receiver() {
    // View(MethodCall(predcell_slice, "index", [i])) should be recognized
    // as a Mapping receiver for subsequent method calls like [x].
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));
    let index_expr = method_call(receiver, "index", vec![int(0)]);
    let view_expr = view(index_expr);

    let encoder = AYEncoder::new();
    assert!(
        encoder.is_mapping_receiver(&view_expr, None),
        "View(PredCellSlice.index(i)) should be a Mapping receiver"
    );
}

#[test]
#[timeout(30000)]
fn test_predcell_slice_index_logic_view_is_mapping_receiver() {
    // View(MethodCall(predcell_slice, "index_logic", [i])) should also
    // be recognized as a Mapping receiver.
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));
    let index_expr = method_call(receiver, "index_logic", vec![int(0)]);
    let view_expr = view(index_expr);

    let encoder = AYEncoder::new();
    assert!(
        !encoder.is_seq_receiver(&view_expr, None),
        "View(PredCellSlice.index_logic(i)) should not be classified as Seq"
    );
    assert!(
        encoder.is_mapping_receiver(&view_expr, None),
        "View(PredCellSlice.index_logic(i)) should be a Mapping receiver"
    );
}

// ── PredCellSlice view encoding produces dedicated UF ──

#[test]
#[timeout(30000)]
fn test_predcell_slice_indexed_view_encodes_with_dedicated_uf() {
    // View(MethodCall(predcell_slice, "index", [0])) should use the
    // dedicated __predcell_slice_elem_view UF instead of the generic
    // view/logic_fn path. This ensures sort-correct encoding.
    let mut encoder = AYEncoder::new();
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));
    let index_expr = method_call(receiver, "index", vec![int(0)]);
    let view_expr = view(index_expr);

    let result = encoder.encode_pure(&view_expr);
    assert!(
        result.is_ok(),
        "View(PredCellSlice.index(0)) should encode: {:?}",
        result.err()
    );
    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Mapping".to_string()),
        "PredCellSlice element view should have Mapping sort"
    );
}

// ── Mapping application via index on viewed PredCell ──

#[test]
#[timeout(30000)]
fn test_mapping_get_on_predcell_view() {
    // After View(PredCellSlice.index(0)) produces a Mapping, calling
    // index_logic(x) on it should route to mapping_get.
    let mut encoder = AYEncoder::new();
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let slice_var = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));

    // slice[0]@[x] = View(MethodCall(slice, "index", [0]))[x]
    // = MethodCall(View(MethodCall(slice, "index", [0])), "index_logic", [x])
    let index_expr = method_call(slice_var, "index", vec![int(0)]);
    let view_expr = view(index_expr);
    let apply_mapping = method_call(view_expr, "index_logic", vec![var("x")]);

    let result = encoder.encode_pure(&apply_mapping);
    assert!(
        result.is_ok(),
        "Mapping get on PredCell view should encode: {:?}",
        result.err()
    );
}

// ── PermCell view is identity (T) ──

#[test]
#[timeout(30000)]
fn test_permcell_view_encodes() {
    // View(Var("pc", PermCell)) should encode successfully.
    // PermCell<T>.view() : T, so view is a value accessor.
    let mut encoder = AYEncoder::new();
    let permcell_id = intern_sort_name("PermCell");
    let pc_var = var_with_sort("pc", ExprSort::Datatype(permcell_id));
    let pc_view = view(pc_var);

    let result = encoder.encode_pure(&pc_view);
    assert!(
        result.is_ok(),
        "View(PermCell) should encode: {:?}",
        result.err()
    );
}

// ── PermCell borrow postcondition: *result == self@ ──

#[test]
#[timeout(30000)]
fn test_permcell_borrow_postcondition_pattern() {
    // The PermCell::borrow postcondition is: *result == self@
    // This creates: Eq(Deref(Var("result")), View(Var("self")))
    let mut encoder = AYEncoder::new();
    let deref_result = deref(var("result"));
    let permcell_id = intern_sort_name("PermCell");
    let view_self = view(var_with_sort(
        "self",
        ExprSort::Ref(Box::new(ExprSort::Datatype(permcell_id))),
    ));
    let postcond = eq(deref_result, view_self);

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "PermCell borrow postcondition should encode: {:?}",
        result.err()
    );
}

// ── PermCell replace postcondition: result == self@ && (^self)@ == value ──

#[test]
#[timeout(30000)]
fn test_permcell_replace_postcondition_pattern() {
    // The PermCell::replace postcondition is:
    //   result == self@ && (^self)@ == value
    let mut encoder = AYEncoder::new();
    let permcell_id = intern_sort_name("PermCell");
    let self_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(permcell_id)));

    let result_eq_view = eq(
        var("result"),
        view(var_with_sort("self", self_sort.clone())),
    );
    let final_view_eq_val = eq(
        view(final_expr(var_with_sort("self", self_sort))),
        var("value"),
    );
    let postcond = and(result_eq_view, final_view_eq_val);

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "PermCell replace postcondition should encode: {:?}",
        result.err()
    );
}

// ── PredCell new postcondition: result@ == *_pred ──

#[test]
#[timeout(30000)]
fn test_predcell_new_postcondition_pattern() {
    // The PredCell::new postcondition is: result@ == *_pred
    // View(result) should produce a Mapping.
    let mut encoder = AYEncoder::new();
    let view_result = view(var("result"));
    let deref_pred = deref(var("_pred"));
    let postcond = eq(view_result, deref_pred);

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "PredCell new postcondition should encode: {:?}",
        result.err()
    );
}

// ── PredCell get postcondition in Bool context: self@[result] ──

#[test]
#[timeout(30000)]
fn test_predcell_get_postcondition_bool_context() {
    // The PredCell::get postcondition is: self@[result]
    // This is a Bool-context expression: the Mapping applied to result.
    // MethodCall(View(self), "index", [result]) in Bool context.
    let mut encoder = AYEncoder::new();
    let predcell_id = intern_sort_name("PredCell");
    let self_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(predcell_id)));
    let view_self = view(var_with_sort("self", self_sort));
    let predicate_app = method_call(view_self, "index", vec![var("result")]);

    // In Bool context, this should encode as a Bool predicate.
    let result = encoder.encode_bool_context_operand(&predicate_app, None);
    assert!(
        result.is_ok(),
        "PredCell get postcondition (Bool context) should encode: {:?}",
        result.err()
    );
}

// ── PredCell set precondition: self@[value] ──

#[test]
#[timeout(30000)]
fn test_predcell_set_precondition_pattern() {
    // The PredCell::set precondition is: self@[value]
    // Same as get postcondition but with value instead of result.
    let mut encoder = AYEncoder::new();
    let predcell_id = intern_sort_name("PredCell");
    let self_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(predcell_id)));
    let view_self = view(var_with_sort("self", self_sort));
    let predicate_app = method_call(view_self, "index", vec![var("value")]);

    let result = encoder.encode_bool_context_operand(&predicate_app, None);
    assert!(
        result.is_ok(),
        "PredCell set precondition should encode: {:?}",
        result.err()
    );
}

// ── Quantified PredCell predicate: forall<x> pred@[x] == ... ──

#[test]
#[timeout(30000)]
fn test_quantified_predcell_predicate() {
    // The PredCell::swap precondition uses:
    //   forall<x: _> self@[x] == other@[x]
    // This requires quantifier-bound variable x applied to a Mapping.
    let mut encoder = AYEncoder::new();
    let predcell_id = intern_sort_name("PredCell");
    let self_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(predcell_id)));
    let view_self = view(var_with_sort("self", self_sort.clone()));
    let view_other = view(var_with_sort("other", self_sort));

    let self_at_x = method_call(view_self, "index", vec![var("x")]);
    let other_at_x = method_call(view_other, "index", vec![var("x")]);
    let body = eq(self_at_x, other_at_x);
    let formula = forall("x", body);

    let result = encoder.encode_pure(&formula);
    assert!(
        result.is_ok(),
        "Quantified PredCell predicate should encode: {:?}",
        result.err()
    );
}

// ── as_slice_of_cells postcondition patterns ──

#[test]
#[timeout(30000)]
fn test_as_slice_of_cells_len_postcondition() {
    // ensures: result@.len() == _pred.len()
    let mut encoder = AYEncoder::new();
    let view_result = view(var("result"));
    let len_result = method_call(view_result, "len", vec![]);
    let len_pred = method_call(var("_pred"), "len", vec![]);
    let postcond = eq(len_result, len_pred);

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "as_slice_of_cells len postcondition should encode: {:?}",
        result.err()
    );
}

#[test]
#[timeout(30000)]
fn test_as_slice_of_cells_elem_view_eq_postcondition() {
    // ensures: forall<i: Int> 0 <= i && i < _pred.len() ==> result[i]@ == _pred[i]
    // This requires:
    //   1. result[i] to be recognized as PredCellSlice indexing
    //   2. View(result[i]) to produce a Mapping-sorted term
    //   3. _pred[i] to also produce a Mapping-sorted term (Seq of Mapping)
    let mut encoder = AYEncoder::new();
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let result_var = var_with_sort("result", ExprSort::Datatype(predcell_slice_id));

    let result_i = method_call(result_var, "index", vec![var("i")]);
    let view_result_i = view(result_i);
    let pred_i = method_call(var("_pred"), "index_logic", vec![var("i")]);
    let eq_clause = eq(view_result_i, pred_i);

    let guard = and(
        ge(var("i"), int(0)),
        lt(var("i"), method_call(var("_pred"), "len", vec![])),
    );
    let body = implies(guard, eq_clause);
    let formula = forall("i", body);

    let result = encoder.encode_pure(&formula);
    assert!(
        result.is_ok(),
        "as_slice_of_cells elem view eq postcondition should encode: {:?}",
        result.err()
    );
}

#[test]
#[timeout(30000)]
fn test_as_slice_of_cells_predicate_pointwise_postcondition() {
    // ensures: forall<i: Int, x: _> 0 <= i && i < _pred.len()
    //          ==> result[i]@[x] == _pred[i][x]
    // This is the most complex PredCell encoding path: nested quantifiers
    // with Mapping application through PredCellSlice indexing.
    let mut encoder = AYEncoder::new();
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let result_var = var_with_sort("result", ExprSort::Datatype(predcell_slice_id));

    // result[i]@[x]
    let result_i = method_call(result_var, "index", vec![var("i")]);
    let view_result_i = view(result_i);
    let result_i_at_x = method_call(view_result_i, "index_logic", vec![var("x")]);

    // _pred[i][x]
    let pred_i = method_call(var("_pred"), "index_logic", vec![var("i")]);
    let pred_i_at_x = method_call(pred_i, "index_logic", vec![var("x")]);

    let eq_clause = eq(result_i_at_x, pred_i_at_x);
    let guard = and(
        ge(var("i"), int(0)),
        lt(var("i"), method_call(var("_pred"), "len", vec![])),
    );
    let body = implies(guard, eq_clause);
    let formula_inner = forall("x", body);
    let formula = forall("i", formula_inner);

    let result = encoder.encode_pure(&formula);
    assert!(
        result.is_ok(),
        "as_slice_of_cells predicate pointwise postcondition should encode: {:?}",
        result.err()
    );
}

// ── PermCell new returns tuple: result.0@ == value ──

#[test]
#[timeout(30000)]
fn test_permcell_new_tuple_postcondition() {
    // PermCell::new postcondition: result.0@ == value
    // This is a tuple projection followed by view.
    let mut encoder = AYEncoder::new();
    let field_0 = get_field(0, var("result"));
    let view_field_0 = view(field_0);
    let postcond = eq(view_field_0, var("value"));

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "PermCell new tuple postcondition should encode: {:?}",
        result.err()
    );
}

// ── PermCell borrow_mut postcondition: *result == self@ && ^result == (^self)@ ──

#[test]
#[timeout(30000)]
fn test_permcell_borrow_mut_postcondition_pattern() {
    // borrow_mut: ensures *result == self@ && ^result == (^self)@
    let mut encoder = AYEncoder::new();
    let permcell_id = intern_sort_name("PermCell");
    let self_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(permcell_id)));

    let current_eq = eq(
        deref(var("result")),
        view(var_with_sort("self", self_sort.clone())),
    );
    let final_eq = eq(
        final_expr(var("result")),
        view(final_expr(var_with_sort("self", self_sort))),
    );
    let postcond = and(current_eq, final_eq);

    let result = encoder.encode_pure(&postcond);
    assert!(
        result.is_ok(),
        "PermCell borrow_mut postcondition should encode: {:?}",
        result.err()
    );
}

// ── Closure-Mapping equality for PredCell preconditions ──

#[test]
#[timeout(30000)]
fn test_predcell_view_eq_closure_produces_mapping_equality() {
    // The PredCell precondition pattern: c@ == |z: u32| z@ % 2 == 0
    // View(Var("c", PredCell)) == Closure(|z| z@ % 2 == 0)
    //
    // Without the closure-mapping equality fix, the closure encodes as an
    // unconstrained __closure_logic_0: Bool instead of a proper Mapping
    // constant with a defining axiom. This test verifies the fix. (#2316)
    use std::sync::Arc;

    let mut encoder = AYEncoder::new();
    let predcell_id = intern_sort_name("PredCell");
    let cell_sort = ExprSort::Ref(Box::new(ExprSort::Datatype(predcell_id)));
    let cell_view = view(var_with_sort("c", cell_sort));

    // Closure: |z: u32| z@ % 2 == 0
    let z_view = view(var("z"));
    let z_mod_2 = PureExpr::BinOp(Arc::new(z_view), BinOp::Mod, Arc::new(int(2)));
    let body = PureExpr::BinOp(Arc::new(z_mod_2), BinOp::Eq, Arc::new(int(0)));
    let closure = PureExpr::Closure {
        params: vec![("z".to_string(), Some(ExprSort::Int))],
        body: Arc::new(body),
    };

    // Precondition: c@ == |z| z@ % 2 == 0
    let precond = eq(cell_view, closure);

    let result = encoder.encode_pure(&precond);
    assert!(
        result.is_ok(),
        "PredCell view == closure should encode: {:?}",
        result.err()
    );

    // The closure side should produce a Mapping-sorted term, not a Bool.
    // After the equality is asserted, mapping_get on the view should be usable.
    let view_cell = view(var_with_sort(
        "c",
        ExprSort::Ref(Box::new(ExprSort::Datatype(predcell_id))),
    ));
    let mapping_app = method_call(view_cell, "index_logic", vec![var("v")]);
    let mapping_result = encoder.encode_pure(&mapping_app);
    assert!(
        mapping_result.is_ok(),
        "Mapping application on PredCell view should encode after closure equality: {:?}",
        mapping_result.err()
    );
}

// ── PredCellSlice index sort inference via public API ──

#[test]
#[timeout(30000)]
fn test_predcell_slice_index_view_infers_mapping_sort() {
    // View(MethodCall(PredCellSlice, "index", [0])) should infer Mapping sort
    // through the public infer_expr_sort_with_context API.
    let mut encoder = AYEncoder::new();
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));
    let index_call = method_call(receiver, "index", vec![int(0)]);
    let view_index = view(index_call);

    let sort = encoder.infer_expr_sort_with_context(&view_index, None);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Mapping".to_string()),
        "View(PredCellSlice.index(0)) should infer Mapping sort"
    );
}

#[test]
#[timeout(30000)]
fn test_non_predcell_index_does_not_infer_mapping() {
    // View(MethodCall(Vec, "index", [0])) should NOT infer Mapping sort.
    let mut encoder = AYEncoder::new();
    let vec_id = intern_sort_name("Vec");
    let receiver = var_with_sort("v", ExprSort::Datatype(vec_id));
    let index_call = method_call(receiver, "index", vec![int(0)]);
    let view_index = view(index_call);

    let sort = encoder.infer_expr_sort_with_context(&view_index, None);
    assert_ne!(
        sort,
        Sort::Uninterpreted("Mapping".to_string()),
        "View(Vec.index(0)) should NOT infer Mapping sort"
    );
}

// ── PredCell receiver classification via is_mapping_receiver ──

#[test]
#[timeout(30000)]
fn test_predcell_slice_view_index_is_mapping_receiver_via_encoder() {
    // Test the is_mapping_receiver classification through AYEncoder.
    let encoder = AYEncoder::new();
    let predcell_slice_id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("slice", ExprSort::Datatype(predcell_slice_id));
    let index_call = method_call(receiver, "index", vec![int(0)]);
    let view_index = view(index_call);

    assert!(
        encoder.is_mapping_receiver(&view_index, None),
        "View(PredCellSlice.index(0)) should be classified as Mapping receiver"
    );
}

#[test]
#[timeout(30000)]
fn test_non_predcell_view_index_not_mapping_receiver() {
    let encoder = AYEncoder::new();
    let vec_id = intern_sort_name("Vec");
    let receiver = var_with_sort("v", ExprSort::Datatype(vec_id));
    let index_call = method_call(receiver, "index", vec![int(0)]);
    let view_index = view(index_call);

    assert!(
        !encoder.is_mapping_receiver(&view_index, None),
        "View(Vec.index(0)) should NOT be classified as Mapping receiver"
    );
}
