// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for operator encoding, sort coercion, and Bool/Int safety nets.

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::{
    formula::{BinOp, ExprSort, FloatBits, PureExpr, UnOp},
    logic::{LogicFnDef, LogicMode},
};

use crate::{
    encoder::{unsoundness, AYEncoder},
    tests::helpers::{
        add, binop, bool_expr, deref, div, eq, get_field, implies, int, ite, le, let_assume, mul,
        ne, sub, var, var_with_sort,
    },
};

fn float(value: f64) -> PureExpr {
    PureExpr::Float(FloatBits::from_f64(value))
}

/// Shared-reference deref is a pure immutable value read, not mutable-borrow
/// temporal state. It must stay connected to the argument variable instead of
/// introducing an unconstrained `*_current` symbol.
#[test]
#[timeout(30000)]
fn test_shared_ref_deref_collapses_to_base_var() {
    let mut encoder = AYEncoder::new_pure();
    let expr = deref(var_with_sort("b", ExprSort::Ref(Box::new(ExprSort::Bool))));

    let term = encoder
        .encode_pure(&expr)
        .expect("shared-ref deref should encode through the base variable");

    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);
    assert!(
        encoder.var_term("b").is_some(),
        "shared-ref deref should declare the base variable"
    );
    assert!(
        encoder.var_term("b_current").is_none(),
        "shared-ref deref must not create mutable-borrow temporal state"
    );
}

/// Reflexive comparison of identical non-numeric terms must be UNSAT when negated.
///
/// Before #2285 fix: `field(x) <= field(x)` encoded each side as a *different*
/// fresh Int constant, so `NOT(fresh0 <= fresh1)` was satisfiable — producing a
/// spurious counterexample for the tautology `x.a <= x.a`.
///
/// After fix: `coerce_to_numeric` reuses the same fresh Int constant when
/// both operands are the same ay term, preserving reflexivity.
#[test]
#[timeout(30000)]
fn test_reflexive_non_numeric_comparison_is_tautology() {
    let mut encoder = AYEncoder::new();

    // Build `__trust_wp_tuple_get_0(x) <= __trust_wp_tuple_get_0(x)` where x has
    // a non-numeric sort, matching the actual field-access lowering surface.
    let x = var_with_sort(
        "x",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("X")),
    );
    let field_access = get_field(0, x);
    let reflexive_le = le(field_access.clone(), field_access);

    let term = encoder
        .encode_pure(&reflexive_le)
        .expect("reflexive Le on non-Int field should encode");

    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

    // Negate: NOT(field(x) <= field(x)) should be UNSAT (it's a tautology).
    let negated = encoder.solver.not(term);
    encoder.solver.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(field(x) <= field(x)) must be UNSAT — reflexive comparison is a tautology (#2285)"
    );
}

/// Int-sorted operands in And/Or/Implies/Not are coerced to Bool via `!= 0`.
///
/// Before this fix: `implies(Int, Bool)` panicked with "sort mismatch in
/// not: expected Bool, got Int". This test verifies the encoding completes
/// and produces a Bool-sorted term for all four logical connectives.
///
/// (#994: Bool/Int confusion — `02_fib`, `such_that`, `09_capacity`)
#[test]
#[timeout(30000)]
fn test_bool_coercion_for_int_operands_in_logical_ops() {
    let mut encoder = AYEncoder::new();

    // Declare an Int variable directly to simulate sort fallback.
    let x_term = encoder.solver.declare_const("x", Sort::Int);
    let y_term = encoder.solver.declare_const("y", Sort::Bool);

    // And(Int, Bool) — should not panic.
    let (l, r) = encoder.coerce_bool_operands(x_term, y_term);
    assert_eq!(encoder.solver.get_sort(l), Sort::Bool);
    assert_eq!(encoder.solver.get_sort(r), Sort::Bool);
    let and_term = encoder.solver.and(l, r);
    assert_eq!(encoder.solver.get_sort(and_term), Sort::Bool);

    // Not(Int) — should not panic.
    let coerced = encoder.coerce_bool_operand(x_term);
    assert_eq!(encoder.solver.get_sort(coerced), Sort::Bool);
    let not_term = encoder.solver.not(coerced);
    assert_eq!(encoder.solver.get_sort(not_term), Sort::Bool);

    // Implies via encode_binop: build PureExpr path.
    let implies_expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("a".to_string(), None)),
        BinOp::Implies,
        Arc::new(PureExpr::Bool(true)),
    );
    let result = encoder.encode_pure(&implies_expr);
    assert!(
        result.is_ok(),
        "Implies with unresolved Var should not panic: {result:?}"
    );
    assert_eq!(encoder.solver.get_sort(result.unwrap()), Sort::Bool);

    // Not via encode_pure.
    let not_expr = PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Var("b".to_string(), None)));
    let result = encoder.encode_pure(&not_expr);
    assert!(
        result.is_ok(),
        "Not with unresolved Var should not panic: {result:?}"
    );
    assert_eq!(encoder.solver.get_sort(result.unwrap()), Sort::Bool);
}

/// Bool hints can outrun the actual ay term sort when a variable is already
/// declared as Int in the encoder state. Equality must consult actual term
/// sorts before taking the manual iff path, or ay panics on `implies(Int, Bool)`.
#[test]
#[timeout(30000)]
fn test_bool_hint_on_int_var_equality_uses_actual_term_sorts() {
    let mut encoder = AYEncoder::new();
    let x_name = "__bool_hint_gap_x";
    let x = encoder.solver.declare_const(x_name, Sort::Int);
    encoder.insert_var(x_name.to_string(), x);
    encoder.insert_var_sort(x_name.to_string(), Sort::Int);
    encoder.record_sort_hint(x_name.to_string(), ExprSort::Bool);

    let expr = eq(var(x_name), bool_expr(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool-hinted Int variable equality should encode without panic");
    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);
    assert!(
        encoder.solver_panic_reason().is_none(),
        "actual-sort guard should avoid solver panic for Bool-hinted Int equality"
    );

    let one = encoder.solver.int_const(1);
    let x_is_one = encoder.solver.eq(x, one);
    encoder.solver.assert_term(x_is_one);
    let not_term = encoder.solver.not(term);
    encoder.solver.assert_term(not_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x == true should reduce to x == 1 when the actual ay term sort is Int"
    );
}

fn logic_call_expr(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

fn int_truncate_expr(name: &str, value: PureExpr) -> PureExpr {
    logic_call_expr(name, vec![value])
}

fn no_arg_method_call(receiver: PureExpr, method: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args: vec![],
    }
}

fn register_single_bit_test_logic_fn(encoder: &mut AYEncoder, name: &str) {
    let bitvec = var("bitvec");
    let bit = var("bit");
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(bit));
    let masked = PureExpr::BinOp(Arc::new(bitvec), BinOp::BitAnd, Arc::new(mask));
    let body = ne(masked, int(0));
    let logic_fn = LogicFnDef::new(
        name.to_string(),
        format!("crate::{name}"),
        vec!["bitvec".to_string(), "bit".to_string()],
        body,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int), Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register single-bit test logic function");
}

#[test]
#[timeout(30000)]
fn test_open_logic_body_equality_uses_recorded_result_alias_without_quantifier() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let val = var_with_sort("val", ExprSort::Int);
    let leading_zeros = no_arg_method_call(val.clone(), "leading_zeros_logic");
    let body = PureExpr::BinOp(Arc::new(int(64)), BinOp::Sub, Arc::new(leading_zeros));
    let logic_fn = LogicFnDef::new(
        "ffs_logic".to_string(),
        "crate::ffs_logic".to_string(),
        vec!["val".to_string()],
        body.clone(),
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register ffs-style logic function");

    let body_term = encoder
        .encode_pure(&body)
        .expect("body expression should encode");
    encoder.rebind_var("result", body_term, Sort::Int);
    encoder.record_var_expr_alias("result", body.clone());

    let postcondition = eq(var("result"), logic_call_expr("ffs_logic", vec![val]));
    let encoded = encoder
        .encode_pure(&postcondition)
        .expect("result alias equality should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "result == ffs_logic(val) should reduce through the open defining body"
    );
}

#[test]
#[timeout(30000)]
fn test_open_logic_body_equality_folds_usize_bits_const() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let val = var_with_sort("ffs_const_val", ExprSort::Int);
    let leading_zeros = no_arg_method_call(val.clone(), "leading_zeros_logic");
    let body_with_const = PureExpr::BinOp(
        Arc::new(var("USIZE_BITS")),
        BinOp::Sub,
        Arc::new(leading_zeros.clone()),
    );
    let logic_fn = LogicFnDef::new(
        "ffs_logic_usize_bits".to_string(),
        "crate::ffs_logic_usize_bits".to_string(),
        vec!["val".to_string()],
        body_with_const,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register ffs-style logic function with USIZE_BITS");

    let usize_bits = int((std::mem::size_of::<usize>() * 8) as i64);
    let extracted_body = PureExpr::BinOp(Arc::new(usize_bits), BinOp::Sub, Arc::new(leading_zeros));
    let body_term = encoder
        .encode_pure(&extracted_body)
        .expect("body expression should encode");
    encoder.rebind_var("result", body_term, Sort::Int);
    encoder.record_var_expr_alias("result", extracted_body);

    let postcondition = eq(
        var("result"),
        logic_call_expr("ffs_logic_usize_bits", vec![val]),
    );
    let encoded = encoder
        .encode_pure(&postcondition)
        .expect("result alias equality should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);
    assert!(
        encoder.var_term("USIZE_BITS").is_none(),
        "USIZE_BITS should fold before encoding the open logic equality"
    );

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "USIZE_BITS in an open logic body should normalize to the concrete usize width"
    );
}

#[test]
#[timeout(30000)]
fn test_open_logic_body_equality_does_not_inline_guarded_definition() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = var_with_sort("guarded_x", ExprSort::Int);
    let body = add(x.clone(), int(1));
    let requires = PureExpr::BinOp(Arc::new(x.clone()), BinOp::Gt, Arc::new(int(0)));
    let logic_fn = LogicFnDef::new_with_requires(
        "guarded_inc".to_string(),
        "crate::guarded_inc".to_string(),
        vec!["guarded_x".to_string()],
        vec![requires],
        body.clone(),
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register guarded logic function");

    let body_term = encoder
        .encode_pure(&body)
        .expect("guarded body expression should encode");
    encoder.rebind_var("result", body_term, Sort::Int);
    encoder.record_var_expr_alias("result", body);

    let postcondition = eq(
        var("result"),
        logic_call_expr("guarded_inc", vec![x.clone()]),
    );
    let encoded = encoder
        .encode_pure(&postcondition)
        .expect("guarded equality should encode");
    let x_term = encoder
        .encode_pure(&x)
        .expect("guarded variable should encode");
    let minus_one = encoder.solver.int_const(-1);
    let x_is_minus_one = encoder.solver.eq(x_term, minus_one);
    encoder.solver.assert_term(x_is_minus_one);
    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "guarded definitions must remain satisfiable unless their requires are known, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_open_logic_body_equality_keeps_symbolic_mod_opaque_in_quantifier_scope() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let body = binop(var("k"), BinOp::Mod, var("n"));
    let logic_fn = LogicFnDef::new(
        "bucket_ix_qguard".to_string(),
        "crate::bucket_ix_qguard".to_string(),
        vec!["k".to_string(), "n".to_string()],
        body,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int), Some(ExprSort::Int)])
    .with_return_sort(Some(ExprSort::Int));
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register symbolic-mod logic function");

    let equality = eq(
        logic_call_expr("bucket_ix_qguard", vec![var("qk"), var("qn")]),
        var("qi"),
    );
    encoder.quantifier_state.inc_quantifier_depth();
    let encoded = encoder
        .encode_pure(&equality)
        .expect("quantified-scope symbolic-mod equality should encode");
    encoder.quantifier_state.dec_quantifier_depth();

    let rendered = encoder.solver.format_term(encoded);
    assert!(
        rendered.contains("logic_bucket__ix__qguard"),
        "quantified-scope equality should keep the logic-function UF pattern, got {rendered}"
    );
    assert!(
        !rendered.contains("mod"),
        "quantified-scope equality must not inline symbolic mod, got {rendered}"
    );
}

#[test]
#[timeout(30000)]
fn test_open_logic_body_equality_folds_constant_int_truncation() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let val = var_with_sort("ffs_cast_val", ExprSort::Int);
    let leading_zeros = no_arg_method_call(val.clone(), "leading_zeros_logic");
    let body_with_cast = PureExpr::BinOp(
        Arc::new(int_truncate_expr("__trust_wp_int_truncate_u32", int(64))),
        BinOp::Sub,
        Arc::new(leading_zeros.clone()),
    );
    let logic_fn = LogicFnDef::new(
        "ffs_logic_cast".to_string(),
        "crate::ffs_logic_cast".to_string(),
        vec!["val".to_string()],
        body_with_cast,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register ffs-style logic function with const cast");

    let extracted_body = PureExpr::BinOp(Arc::new(int(64)), BinOp::Sub, Arc::new(leading_zeros));
    let body_term = encoder
        .encode_pure(&extracted_body)
        .expect("body expression should encode");
    encoder.rebind_var("result", body_term, Sort::Int);
    encoder.record_var_expr_alias("result", extracted_body);

    let postcondition = eq(var("result"), logic_call_expr("ffs_logic_cast", vec![val]));
    let encoded = encoder
        .encode_pure(&postcondition)
        .expect("result alias equality should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "constant int truncation in an open logic body should fold before equality comparison"
    );
}

#[test]
#[timeout(30000)]
fn test_constant_int_truncation_encodes_without_symbolic_bv_condition() {
    let mut encoder = AYEncoder::new();
    let expr = eq(
        int_truncate_expr("__trust_wp_int_truncate_u32", int(64)),
        int(64),
    );
    let encoded = encoder
        .encode_pure(&expr)
        .expect("constant int truncation equality should encode");
    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "64 as u32 should fold to 64"
    );
}

#[test]
#[timeout(30000)]
fn test_ffs_style_empty_nonzero_postcondition_uses_ground_range_facts() {
    use num_bigint::BigInt;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let val = var_with_sort("empty_val", ExprSort::Int);
    let leading_zeros = no_arg_method_call(var("val"), "leading_zeros_logic");
    let body = PureExpr::BinOp(
        Arc::new(var("USIZE_BITS")),
        BinOp::Sub,
        Arc::new(leading_zeros),
    );
    let logic_fn = LogicFnDef::new(
        "ffs_logic".to_string(),
        "crate::ffs_logic".to_string(),
        vec!["val".to_string()],
        body,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register ffs-style logic function");

    let val_term = encoder.encode_pure(&val).expect("encode usize value");
    let zero = encoder.solver.int_const(0);
    let usize_max = (BigInt::from(1u8) << (std::mem::size_of::<usize>() * 8)) - BigInt::from(1u8);
    let usize_max_term = encoder.solver.int_const_bigint(&usize_max);
    let ge_zero = encoder.solver.ge(val_term, zero);
    let le_max = encoder.solver.le(val_term, usize_max_term);
    encoder.assert_term(ge_zero);
    encoder.assert_term(le_max);

    let ffs = logic_call_expr("ffs_logic", vec![val.clone()]);
    let ffs_minus_one = sub(ffs.clone(), int(1));
    let truncated_shift = int_truncate_expr("__trust_wp_int_truncate_u8", ffs_minus_one.clone());
    let shifted_truncated = binop(int(1), BinOp::Shl, truncated_shift.clone());
    let cleared_truncated = binop(
        val.clone(),
        BinOp::BitAnd,
        PureExpr::UnOp(UnOp::BitNot, Arc::new(shifted_truncated)),
    );
    let return_expr = ite(
        eq(ffs.clone(), int(0)),
        int(0),
        let_assume(
            binop(truncated_shift, BinOp::Lt, int(64)),
            cleared_truncated.clone(),
        ),
    );
    let return_term = encoder
        .encode_pure(&return_expr)
        .expect("encode empty-style return expression");
    encoder.rebind_var("result", return_term, Sort::Int);
    encoder.record_var_expr_alias("result", return_expr);

    let shifted_spec = binop(int(1), BinOp::Shl, ffs_minus_one);
    let cleared_spec = binop(
        val.clone(),
        BinOp::BitAnd,
        PureExpr::UnOp(UnOp::Not, Arc::new(shifted_spec)),
    );
    let postcondition = implies(ne(val, int(0)), eq(var("result"), cleared_spec));
    let encoded = encoder
        .encode_pure(&postcondition)
        .expect("encode empty nonzero postcondition");
    let negated = encoder.solver.not(encoded);
    encoder.assert_term(negated);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "nonzero empty postcondition should verify from ffs range and truncation identity facts, got {sat:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_ffs_style_empty_zero_postcondition_uses_ite_zero_branch_fact() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let val = var_with_sort("empty_val", ExprSort::Int);
    let leading_zeros = no_arg_method_call(var("val"), "leading_zeros_logic");
    let body = PureExpr::BinOp(
        Arc::new(var("USIZE_BITS")),
        BinOp::Sub,
        Arc::new(leading_zeros),
    );
    let logic_fn = LogicFnDef::new(
        "ffs_logic".to_string(),
        "crate::ffs_logic".to_string(),
        vec!["val".to_string()],
        body,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)]);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register ffs-style logic function");

    let ffs = logic_call_expr("ffs_logic", vec![val.clone()]);
    let ffs_minus_one = sub(ffs.clone(), int(1));
    let truncated_shift = int_truncate_expr("__trust_wp_int_truncate_u8", ffs_minus_one);
    let shifted_truncated = binop(int(1), BinOp::Shl, truncated_shift.clone());
    let cleared_truncated = binop(
        val.clone(),
        BinOp::BitAnd,
        PureExpr::UnOp(UnOp::BitNot, Arc::new(shifted_truncated)),
    );
    let return_expr = ite(
        eq(ffs, int(0)),
        int(0),
        let_assume(
            binop(truncated_shift, BinOp::Lt, int(64)),
            cleared_truncated,
        ),
    );
    let return_term = encoder
        .encode_pure(&return_expr)
        .expect("encode empty-style return expression");
    encoder.rebind_var("result", return_term, Sort::Int);
    encoder.record_var_expr_alias("result", return_expr);

    let postcondition = implies(eq(val.clone(), int(0)), eq(var("result"), val));
    let encoded = encoder
        .encode_pure(&postcondition)
        .expect("encode empty zero postcondition");
    let negated = encoder.solver.not(encoded);
    encoder.assert_term(negated);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "zero empty postcondition should verify from the ffs zero branch fact, got {sat:?}"
    );
}

/// Non-Int/non-Bool operands in Bool context are replaced with fresh Bool constants.
///
/// This tests the fallback path in `coerce_bool_operand` where a term with
/// Uninterpreted/Seq/Datatype sort appears in a Bool context. The coercion
/// creates an unconstrained Bool constant — a sound but lossy approximation —
/// and increments `BoolCoercionFromNonBool` (non-demoting, split from
/// `SortFallbackToIntFromLogicFn` per #2359).
#[test]
#[timeout(30000)]
fn test_bool_coercion_for_non_int_non_bool_operand() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();

        // Declare a variable with Uninterpreted sort — neither Int nor Bool.
        let ui_term = encoder
            .solver
            .declare_const("ui_var", Sort::Uninterpreted("MyStruct".to_string()));
        assert_eq!(
            encoder.solver.get_sort(ui_term),
            Sort::Uninterpreted("MyStruct".to_string()),
            "precondition: term should have Uninterpreted sort"
        );

        // Coerce to Bool — should not panic, should produce Bool-sorted term.
        let coerced = encoder.coerce_bool_operand(ui_term);
        assert_eq!(
            encoder.solver.get_sort(coerced),
            Sort::Bool,
            "Uninterpreted-sorted term should coerce to Bool"
        );

        // The coerced term should be a fresh constant (unconstrained).
        // Verify it's usable in a logical operation without panic.
        let not_term = encoder.solver.not(coerced);
        assert_eq!(encoder.solver.get_sort(not_term), Sort::Bool);

        // Unsoundness counter should have fired.
        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert_eq!(
            d.get(&unsoundness::UnsoundnessCategory::BoolCoercionFromNonBool),
            Some(&1),
            "coerce_bool_operand on non-Int/non-Bool should increment BoolCoercionFromNonBool: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Int→Bool coercion via `!= 0` should also increment the unsoundness counter.
///
/// This verifies the Int path in `coerce_bool_operand` fires
/// `BoolCoercionFromNonBool` (non-demoting, split from
/// `SortFallbackToIntFromLogicFn` per #2359).
#[test]
#[timeout(30000)]
fn test_bool_coercion_int_operand_fires_unsoundness() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        let int_term = encoder.solver.declare_const("i", Sort::Int);

        let coerced = encoder.coerce_bool_operand(int_term);
        assert_eq!(encoder.solver.get_sort(coerced), Sort::Bool);

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert_eq!(
            d.get(&unsoundness::UnsoundnessCategory::BoolCoercionFromNonBool),
            Some(&1),
            "coerce_bool_operand on Int should increment BoolCoercionFromNonBool: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Bool operand should pass through coerce_bool_operand unchanged, with NO
/// unsoundness counter increment.
#[test]
#[timeout(30000)]
fn test_bool_coercion_bool_operand_no_unsoundness() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        let bool_term = encoder.solver.declare_const("b", Sort::Bool);

        let coerced = encoder.coerce_bool_operand(bool_term);
        assert_eq!(encoder.solver.get_sort(coerced), Sort::Bool);

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert!(
            d.is_empty(),
            "Bool→Bool coercion should not fire unsoundness counter: {d:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

#[test]
#[timeout(30000)]
fn test_float_arithmetic_uses_real_terms() {
    let cases = [
        (
            PureExpr::BinOp(Arc::new(float(1.5)), BinOp::Add, Arc::new(float(2.25))),
            3.75,
        ),
        (
            PureExpr::BinOp(Arc::new(float(5.5)), BinOp::Sub, Arc::new(float(2.0))),
            3.5,
        ),
        (
            PureExpr::BinOp(Arc::new(float(1.5)), BinOp::Mul, Arc::new(float(2.0))),
            3.0,
        ),
        (
            PureExpr::BinOp(Arc::new(float(3.0)), BinOp::Div, Arc::new(float(2.0))),
            1.5,
        ),
    ];

    for (expr, expected) in cases {
        let mut encoder = AYEncoder::new();
        let term = encoder
            .encode_pure(&expr)
            .expect("float arithmetic should encode via Real terms");
        assert_eq!(encoder.solver.get_sort(term), Sort::Real);

        let expected_term = encoder
            .solver
            .try_real_const(expected)
            .expect("expected finite Real literal");
        let neq = encoder.solver.neq(term, expected_term);
        encoder.solver.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "encoded float arithmetic should equal {expected}"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_float_negation_uses_real_arithmetic() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(float(2.5)));
    let term = encoder
        .encode_pure(&expr)
        .expect("float negation should encode via arithmetic negation");

    assert_eq!(encoder.solver.get_sort(term), Sort::Real);

    let expected = encoder
        .solver
        .try_real_const(-2.5)
        .expect("expected finite Real literal");
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded float negation should equal -2.5"
    );
}

#[test]
#[timeout(30000)]
fn test_mixed_int_real_operands_promote_to_real() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::BinOp(Arc::new(PureExpr::Int(1)), BinOp::Add, Arc::new(float(1.5)));
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed Int/Real arithmetic should promote Int to Real");

    assert_eq!(encoder.solver.get_sort(term), Sort::Real);

    let expected = encoder
        .solver
        .try_real_const(2.5)
        .expect("expected finite Real literal");
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "mixed Int/Real arithmetic should evaluate in Real sort"
    );
}

#[test]
#[timeout(30000)]
fn test_float_division_records_real_nonzero_obligation() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::BinOp(
        Arc::new(float(1.0)),
        BinOp::Div,
        Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Float))),
    );

    let term = encoder
        .encode_pure(&expr)
        .expect("float division should encode");
    assert_eq!(encoder.solver.get_sort(term), Sort::Real);
    assert_eq!(
        encoder.arithmetic_mode.division_obligations().len(),
        1,
        "float division should record exactly one nonzero obligation"
    );

    let x = encoder
        .get_or_declare_var("x", Sort::Real)
        .expect("declare x");
    let zero = encoder.solver.rational_const(0, 1);
    let x_is_zero = encoder.solver.eq(x, zero);
    encoder.solver.assert_term(x_is_zero);
    encoder
        .solver
        .assert_term(encoder.arithmetic_mode.division_obligations()[0]);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "real division obligation should rule out x = 0"
    );
}

#[test]
#[timeout(30000)]
fn test_quantified_mod_does_not_leak_division_obligation() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(eq(binop(var("x"), BinOp::Mod, var("i")), int(0))),
        triggers: vec![],
    };

    encoder
        .encode_pure(&expr)
        .expect("quantified modulo expression should encode");

    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "division obligations collected inside quantified bodies would escape bound variables"
    );
}

#[test]
#[timeout(30000)]
fn test_positive_const_div_equality_uses_floor_bounds_for_negative_dividend() {
    let mut encoder = AYEncoder::new();
    let expr = eq(var("q"), div(var("a"), int(2)));
    let term = encoder
        .encode_pure(&expr)
        .expect("positive-constant integer division equality should encode");

    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "division by a positive literal should normalize without a divisor obligation"
    );

    let a = *encoder.vars_for_test().get("a").expect("a declared");
    let q = *encoder.vars_for_test().get("q").expect("q declared");
    let neg_five = encoder.solver.int_const(-5);
    let neg_two = encoder.solver.int_const(-2);
    let a_is_neg_five = encoder.solver.eq(a, neg_five);
    let q_is_neg_two = encoder.solver.eq(q, neg_two);
    encoder.assert_term(term);
    encoder.assert_term(a_is_neg_five);
    encoder.assert_term(q_is_neg_two);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "floor division must reject -5 / 2 == -2"
    );
}

#[test]
#[timeout(30000)]
fn test_positive_const_div_equality_closes_triangular_sum_shape() {
    let mut encoder = AYEncoder::new();
    let n = var("n");
    let result = var("result");
    let product = mul(n.clone(), add(n.clone(), int(1)));
    let invariant = eq(mul(result.clone(), int(2)), product.clone());
    let invariant_term = encoder
        .encode_pure(&invariant)
        .expect("triangular invariant should encode");
    encoder.assert_term(invariant_term);

    let postcondition = eq(result, div(product, int(2)));
    let postcondition_term = encoder
        .encode_pure(&postcondition)
        .expect("triangular division postcondition should encode");

    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "triangular postcondition should avoid native div/UF bridge for / 2"
    );

    let negated_postcondition = encoder.solver.not(postcondition_term);
    encoder.assert_term(negated_postcondition);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "2 * result == n * (n + 1) should imply result == n * (n + 1) / 2"
    );
}

/// fix4-nia-div FIX 2: literal-divisor integer division must NOT emit a native
/// `(div ...)`/`int_div` token (which the LRA bridge marks unsupported ->
/// Unknown). The quotient is a `__trust_wp_int_div` UF application pinned by a
/// linear Euclidean axiom; neither the quotient term nor any asserted term may
/// contain a native builtin `(div ` SMT token.
#[test]
#[timeout(30000)]
fn test_literal_div_emits_no_native_div_token() {
    let mut encoder = AYEncoder::new();
    let expr = div(var("a"), int(2));
    let quotient = encoder.encode_pure(&expr).expect("a / 2 should encode");

    // The quotient itself must be the UF (`__trust_wp_int_div`), never a native
    // builtin `(div ...)` token.
    let rendered_quotient = encoder.solver.format_term(quotient);
    assert!(
        rendered_quotient.contains("__trust_wp_int_div"),
        "literal-divisor quotient should be the __trust_wp_int_div UF, got: {rendered_quotient}"
    );
    assert!(
        !rendered_quotient.contains("(div "),
        "literal-divisor quotient must not contain a native (div ...) token, got: {rendered_quotient}"
    );

    // Sanity: the native builtin token DOES render as `(div `, so the negative
    // assertion above is meaningful.
    let a = *encoder.vars_for_test().get("a").expect("a declared");
    let two = encoder.solver.int_const(2);
    #[allow(deprecated)]
    let native = encoder.solver.int_div(a, two);
    let rendered_native = encoder.solver.format_term(native);
    assert!(
        rendered_native.contains("(div "),
        "precondition: native int_div should render as a (div ...) token, got: {rendered_native}"
    );
}

/// fix4-nia-div FIX 2: a ground literal-divisor obligation `4 / 2 == 2`
/// discharges (negation is UNSAT) through the linear Euclidean axiom, with no
/// native div token and no divisor obligation.
#[test]
#[timeout(30000)]
fn test_literal_div_ground_value_discharges() {
    let mut encoder = AYEncoder::new();
    let expr = eq(div(int(4), int(2)), int(2));
    let term = encoder
        .encode_pure(&expr)
        .expect("4 / 2 == 2 should encode");

    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "division by a positive literal should normalize without a divisor obligation"
    );

    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "4 / 2 == 2 must be a tautology (linear Euclidean axiom pins the quotient)"
    );
}

/// fix4-nia-div FIX 2: a `(n*(n+1))/2`-shaped literal-divisor obligation with a
/// concrete model (n=2 => result 3) discharges through the Euclidean axiom and
/// the combined-mode nonlinear product, mirroring bug/653.
#[test]
#[timeout(30000)]
fn test_literal_div_triangular_concrete_model_discharges() {
    let mut encoder = AYEncoder::new();
    let n = var("n");
    let product = mul(n.clone(), add(n.clone(), int(1)));
    // result == n*(n+1)/2 with n == 2 forces result == 3.
    let postcondition = eq(var("result"), div(product, int(2)));
    let postcondition_term = encoder
        .encode_pure(&postcondition)
        .expect("triangular division postcondition should encode");
    encoder.assert_term(postcondition_term);

    let n_term = *encoder.vars_for_test().get("n").expect("n declared");
    let result_term = *encoder
        .vars_for_test()
        .get("result")
        .expect("result declared");
    let two = encoder.solver.int_const(2);
    let three = encoder.solver.int_const(3);
    let n_is_two = encoder.solver.eq(n_term, two);
    encoder.assert_term(n_is_two);
    // Negate the expected result: result must be 3, so result != 3 is UNSAT.
    let result_ne_three = encoder.solver.neq(result_term, three);
    encoder.assert_term(result_ne_three);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "n=2 => n*(n+1)/2 == 3, so result != 3 must be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_float_comparison_operators() {
    let cases = [
        (BinOp::Lt, float(1.5), float(2.5), true),
        (BinOp::Lt, float(2.5), float(1.5), false),
        (BinOp::Le, float(2.5), float(2.5), true),
        (BinOp::Gt, float(3.0), float(1.0), true),
        (BinOp::Gt, float(1.0), float(3.0), false),
        (BinOp::Ge, float(2.0), float(2.0), true),
    ];
    for (op, l, r, expected) in cases {
        let mut encoder = AYEncoder::new();
        let expr = PureExpr::BinOp(Arc::new(l.clone()), op, Arc::new(r.clone()));
        let term = encoder
            .encode_pure(&expr)
            .unwrap_or_else(|e| panic!("float {op:?} should encode: {e}"));
        assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

        // Assert the opposite of expected and check UNSAT.
        let check = if expected {
            encoder.solver.not(term)
        } else {
            term
        };
        encoder.solver.assert_term(check);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "float {op:?}({l:?}, {r:?}) should be {expected}"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_float_equality_and_inequality() {
    let mut encoder = AYEncoder::new();

    // Eq: 1.5 == 1.5 should be true (negation is UNSAT).
    let eq_expr = PureExpr::BinOp(Arc::new(float(1.5)), BinOp::Eq, Arc::new(float(1.5)));
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("float Eq should encode");
    assert_eq!(encoder.solver.get_sort(eq_term), Sort::Bool);
    let negated = encoder.solver.not(eq_term);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(1.5 == 1.5) should be UNSAT"
    );

    // Ne: 1.5 != 2.5 should be true (negation is UNSAT).
    let mut encoder = AYEncoder::new();
    let ne_expr = PureExpr::BinOp(Arc::new(float(1.5)), BinOp::Ne, Arc::new(float(2.5)));
    let ne_term = encoder
        .encode_pure(&ne_expr)
        .expect("float Ne should encode");
    assert_eq!(encoder.solver.get_sort(ne_term), Sort::Bool);
    let negated = encoder.solver.not(ne_term);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(1.5 != 2.5) should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_mixed_int_float_comparison() {
    let mut encoder = AYEncoder::new();
    // Int(1) < Float(1.5) should be true — Int promoted to Real.
    let expr = PureExpr::BinOp(Arc::new(PureExpr::Int(1)), BinOp::Lt, Arc::new(float(1.5)));
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed Int/Float Lt should encode");
    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

    let negated = encoder.solver.not(term);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(1 < 1.5) should be UNSAT — Int promoted to Real for comparison"
    );
}

/// Mixed Int/Float equality: `Int(2) == Float(2.0)` should be true.
///
/// IntToFloat cast identity (W3 #1802) passes Int PureExpr to Float
/// locals. When these values enter Eq comparisons with Real-sorted terms,
/// `coerce_ite_sorts` must produce `int_to_real` coercion — NOT a fresh
/// unconstrained constant that loses the value relationship.
///
/// Regression guard for the #2353 Int→Real coercion fix in `coerce_ite_sorts`.
/// The encoded equality should now preserve the Int value through `int_to_real`,
/// making the negated formula unsatisfiable.
#[test]
#[timeout(30000)]
fn test_mixed_int_float_equality_coercion_gap() {
    let mut encoder = AYEncoder::new();
    // Int(2) == Float(2.0) — mathematically true, but coerce_ite_sorts
    // replaces the Int term with a fresh unconstrained Real constant.
    let expr = PureExpr::BinOp(Arc::new(PureExpr::Int(2)), BinOp::Eq, Arc::new(float(2.0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed Int/Float Eq should encode");
    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

    let negated = encoder.solver.not(term);
    encoder.solver.assert_term(negated);
    let result = encoder.check_sat();
    // Regression guard: the Int side should be coerced via int_to_real, so
    // 2 == 2.0 is valid and its negation is unsatisfiable.
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT(2 == 2.0) should be Unsat after the Int→Real coercion fix. \
         Got: {result:?}"
    );
}

/// Mixed Int/Float inequality should also preserve the Int value through
/// `int_to_real`; the negation of a true inequality must be unsatisfiable.
#[test]
#[timeout(30000)]
fn test_mixed_int_float_inequality_coercion_gap() {
    let mut encoder = AYEncoder::new();
    // Int(2) != Float(2.5) — mathematically true, but coerce_ite_sorts
    // replaces Int with fresh Real constant, losing the value.
    let expr = PureExpr::BinOp(Arc::new(PureExpr::Int(2)), BinOp::Ne, Arc::new(float(2.5)));
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed Int/Float Ne should encode");
    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

    // The Ne encoding is NOT(eq_or_iff(Int(2), Float(2.5))). After the
    // Int→Real fix, 2 != 2.5 is valid, so negating the whole expression is
    // unsatisfiable.
    let negated = encoder.solver.not(term);
    encoder.solver.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT(2 != 2.5) should be Unsat after the Int→Real coercion fix. \
         Got: {result:?}"
    );
}

#[derive(Clone, Copy)]
enum CoerceIteRelation {
    Eq,
    Neq,
}

fn custom_datatype_sort(name: &str) -> ExprSort {
    ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(name))
}

fn point_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "Point".to_string(),
        AdtDecl::new(
            "crate::Point".to_string(),
            "Point".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Point".to_string(),
                "Point".to_string(),
                vec![AdtFieldDecl::new("x".to_string(), ExprSort::Int)],
            )],
        ),
    )])
}

/// A datatype declaration named `Rc` shaped like the one the driver used to
/// emit for `Rc<T>` before it peeled the wrapper (private fields, no payload).
/// (adtpa)
fn rc_like_adt_decls(adt_name: &str, rust_path: &str) -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        adt_name.to_string(),
        AdtDecl::new(
            rust_path.to_string(),
            adt_name.to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                adt_name.to_string(),
                adt_name.to_string(),
                vec![
                    AdtFieldDecl::new(format!("{adt_name}_ptr"), ExprSort::Int),
                    AdtFieldDecl::new(format!("{adt_name}_phantom"), ExprSort::Int),
                ],
            )],
        ),
    )])
}

#[test]
#[timeout(30000)]
fn test_registered_decl_never_overrides_canonical_int_model_name() {
    // (adtpa) `Rc`/`Arc`/`Box` are transparent wrappers: `Rc<i32>@ : i32`, so
    // their canonical sort is Int (#976, is_int_model_type). If a registered
    // datatype named `Rc` were allowed to win the decl-beats-canonical race
    // (#2652/#2673, which exists for USER ADTs), every `Datatype("Rc")`
    // annotation would resolve to the carrier sort, `rc@ == 1` would become
    // eq(Datatype, Int), and coerce_ite_sorts would swap the literal for a
    // fresh unconstrained constant — fabricating the premise away.
    for (adt_name, rust_path, annotations) in [
        ("Rc", "alloc::rc::Rc", ["alloc::rc::Rc", "Rc"]),
        ("Arc", "alloc::sync::Arc", ["alloc::sync::Arc", "Arc"]),
        ("Box", "alloc::boxed::Box", ["alloc::boxed::Box", "Box"]),
    ] {
        let mut encoder = AYEncoder::new_all();
        encoder.register_adt_decls(&rc_like_adt_decls(adt_name, rust_path));
        for annotation in annotations {
            let sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
                trust_wp_core::formula::intern_sort_name(annotation),
            ));
            assert_eq!(
                sort,
                Sort::Int,
                "a registered `{adt_name}` decl must not override the canonical \
                 Int model sort for annotation {annotation:?}"
            );
        }
    }
}

#[test]
#[timeout(30000)]
fn test_registered_user_adt_still_overrides_canonical_alias() {
    // (adtpa control) The canonical-Int carve-out above must NOT weaken
    // #2652/#2673: user ADTs are canonically `Uninterpreted`, so a registered
    // declaration still wins for them.
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&point_adt_decls());
    encoder.register_adt_decls(&rc_like_adt_decls("Rc", "alloc::rc::Rc"));
    let point_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("crate::Point"),
    ));
    assert!(
        matches!(point_sort, Sort::Datatype(_)),
        "registered user ADT must still resolve to its native datatype sort: {point_sort:?}"
    );
}

fn coerce_ite_relation_result(
    expr: &PureExpr,
    witness: &PureExpr,
    relation: CoerceIteRelation,
) -> (SolveResult, unsoundness::Snapshot) {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new();
    let result_term = encoder
        .encode_pure(expr)
        .expect("ITE coercion witness should encode");
    let witness_term = encoder
        .encode_pure(witness)
        .expect("comparison witness should encode");
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);

    let relation_term = match relation {
        CoerceIteRelation::Eq => encoder.solver.eq(result_term, witness_term),
        CoerceIteRelation::Neq => encoder.solver.neq(result_term, witness_term),
    };
    encoder.solver.assert_term(relation_term);
    let result = encoder.check_sat();
    unsoundness::reset();
    (result, delta)
}

fn assert_coerce_ite_branch_is_conservative_and_tracked(
    expr: &PureExpr,
    witness: &PureExpr,
    branch: &str,
) {
    let (eq_result, eq_delta) = coerce_ite_relation_result(expr, witness, CoerceIteRelation::Eq);
    assert!(
        matches!(eq_result, SolveResult::Sat),
        "{branch}: fresh-constant branch should permit equality with an unconstrained witness"
    );
    assert!(
        !eq_delta.is_empty(),
        "{branch}: coerce_ite_sorts must fire unsoundness counter for fresh-constant path (#2353)"
    );

    let (neq_result, neq_delta) = coerce_ite_relation_result(expr, witness, CoerceIteRelation::Neq);
    assert!(
        matches!(neq_result, SolveResult::Sat),
        "{branch}: fresh-constant branch should also permit disequality with the same witness"
    );
    assert!(
        !neq_delta.is_empty(),
        "{branch}: coerce_ite_sorts must fire unsoundness counter for fresh-constant path (#2353)"
    );
}

/// Unit-vs-other falls back to a fresh constant of the other sort.
/// The unsoundness counter now fires for this approximation (#2353).
#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_unit_to_other_is_conservative_and_tracked() {
    let target_sort = custom_datatype_sort("Target");
    let expr = ite(
        bool_expr(true),
        var_with_sort("u", ExprSort::Unit),
        var_with_sort("x", target_sort.clone()),
    );
    let witness = var_with_sort("x", target_sort);

    assert_coerce_ite_branch_is_conservative_and_tracked(&expr, &witness, "Unit vs other");
}

/// Bool-vs-other discards the Bool value and substitutes a fresh constant of
/// the other sort. The unsoundness counter now fires (#2353).
#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_bool_to_other_is_conservative_and_tracked() {
    let target_sort = custom_datatype_sort("Target");
    let expr = ite(
        bool_expr(true),
        bool_expr(true),
        var_with_sort("x", target_sort.clone()),
    );
    let witness = var_with_sort("x", target_sort);

    assert_coerce_ite_branch_is_conservative_and_tracked(&expr, &witness, "Bool vs other");
}

/// Int-vs-other still uses the fresh-constant approximation for non-Real
/// complex sorts after the Int↔Real carve-out. Counter now fires (#2353).
#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_int_to_other_is_conservative_and_tracked() {
    let target_sort = custom_datatype_sort("Target");
    let expr = ite(
        bool_expr(true),
        int(7),
        var_with_sort("x", target_sort.clone()),
    );
    let witness = var_with_sort("x", target_sort);

    assert_coerce_ite_branch_is_conservative_and_tracked(&expr, &witness, "Int vs other");
}

/// The fallback other-vs-other branch keeps the then-sort and coerces the else
/// arm to a fresh constant of that sort. Counter now fires (#2353).
#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_other_to_other_is_conservative_and_tracked() {
    let left_sort = custom_datatype_sort("Left");
    let right_sort = custom_datatype_sort("Right");
    let expr = ite(
        bool_expr(false),
        var_with_sort("lhs", left_sort.clone()),
        var_with_sort("rhs", right_sort),
    );
    let witness = var_with_sort("lhs", left_sort);

    assert_coerce_ite_branch_is_conservative_and_tracked(
        &expr,
        &witness,
        "other vs other fallback",
    );
}

#[test]
#[timeout(30000)]
fn test_eq_ne_without_explicit_sort_preserve_same_non_int_terms_without_demotion() {
    let handle = std::thread::spawn(|| {
        for op in [BinOp::Eq, BinOp::Ne] {
            unsoundness::reset();
            let before = unsoundness::snapshot();

            let mut encoder = AYEncoder::new();
            let foo_sort = Sort::Uninterpreted("Foo".to_string());
            let left = encoder.solver.declare_const("lhs", foo_sort.clone());
            let right = encoder.solver.declare_const("rhs", foo_sort);
            let term = encoder
                .encode_binop(left, op, right, None)
                .expect("same-sort non-Int equality should encode without fallback");

            assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

            let after = unsoundness::snapshot();
            let delta = unsoundness::delta(&before, &after);
            assert!(
                !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
                "{op:?} without explicit eq_sort should reuse the concrete non-Int term sort: {delta:?}"
            );
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_preserves_option_alias_family_without_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        let rust_sort = Sort::Uninterpreted("Option".to_string());
        let encoded_sort = Sort::Uninterpreted("OptionInt".to_string());
        let rust_term = encoder.solver.declare_const("rust_opt", rust_sort.clone());
        let encoded_term = encoder
            .solver
            .declare_const("encoded_opt", encoded_sort.clone());
        let (lhs, rhs) = super::coerce_ite_sorts(
            &mut encoder.solver,
            rust_term,
            rust_sort,
            encoded_term,
            encoded_sort,
        );

        assert_eq!(
            encoder.solver.get_sort(lhs),
            encoder.solver.get_sort(rhs),
            "related Option/OptionInt branches should converge on one non-Int sort"
        );
        assert_ne!(
            encoder.solver.get_sort(lhs),
            Sort::Int,
            "related Option family branches should not collapse to Int"
        );

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "related Option family branches should not fire SortFallbackToInt: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_preserves_native_datatype_vs_uninterpreted_family_without_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new_all();
        encoder.register_adt_decls(&point_adt_decls());
        let native_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(
            trust_wp_core::formula::intern_sort_name("crate::Point"),
        ));
        assert!(
            matches!(native_sort, Sort::Datatype(_)),
            "Point should resolve to a native datatype sort: {native_sort:?}"
        );

        let bare_sort = Sort::Uninterpreted("Point".to_string());
        let native_term = encoder
            .solver
            .declare_const("native_point", native_sort.clone());
        let bare_term = encoder
            .solver
            .declare_const("bare_point", bare_sort.clone());
        let (lhs, rhs) = super::coerce_ite_sorts(
            &mut encoder.solver,
            native_term,
            native_sort,
            bare_term,
            bare_sort,
        );

        assert_eq!(
            encoder.solver.get_sort(lhs),
            encoder.solver.get_sort(rhs),
            "native datatype and bare datatype branches should converge on one sort family"
        );
        assert_ne!(
            encoder.solver.get_sort(lhs),
            Sort::Int,
            "native datatype vs bare datatype branches should not collapse to Int"
        );

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "native datatype vs bare datatype branches should not fire SortFallbackToInt: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_preserves_mutref_int_vs_int_without_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new_all();
        let mutref_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let inner_sort = Sort::Int;
        let mutref_term = encoder
            .solver
            .declare_const("mutref_int", mutref_sort.clone());
        let int_term = encoder.solver.declare_const("plain_int", inner_sort);
        let (lhs, rhs) = super::coerce_ite_sorts(
            &mut encoder.solver,
            mutref_term,
            mutref_sort.clone(),
            int_term,
            Sort::Int,
        );

        assert_eq!(
            encoder.solver.get_sort(lhs),
            encoder.solver.get_sort(rhs),
            "MutRef(Int) and Int branches should converge on one carrier sort"
        );
        assert_eq!(
            encoder.solver.get_sort(lhs),
            mutref_sort,
            "the MutRef carrier sort should stay authoritative for branch merging"
        );

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "MutRef(Int) vs Int should not fire SortFallbackToInt: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

#[test]
#[timeout(30000)]
fn test_coerce_ite_sorts_preserves_mutref_datatype_vs_datatype_without_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new_all();
        let dt_id = trust_wp_core::formula::intern_sort_name("crate::IterState");
        let bare_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(dt_id));
        let mutref_sort =
            encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Datatype(dt_id))));
        let mutref_term = encoder
            .solver
            .declare_const("mutref_iter", mutref_sort.clone());
        let bare_term = encoder
            .solver
            .declare_const("iter_state", bare_sort.clone());
        let (lhs, rhs) = super::coerce_ite_sorts(
            &mut encoder.solver,
            mutref_term,
            mutref_sort.clone(),
            bare_term,
            bare_sort,
        );

        assert_eq!(
            encoder.solver.get_sort(lhs),
            encoder.solver.get_sort(rhs),
            "MutRef(datatype) and datatype branches should converge on one carrier sort"
        );
        assert_eq!(
            encoder.solver.get_sort(lhs),
            mutref_sort,
            "the MutRef carrier sort should stay authoritative for datatype branch merging"
        );

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "MutRef(datatype) vs datatype should not fire SortFallbackToInt: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

#[test]
#[timeout(30000)]
fn test_datatype_arithmetic_still_records_sort_fallback_to_int() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        let x = var_with_sort(
            "x",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("X")),
        );
        let term = encoder
            .encode_pure(&add(x.clone(), x))
            .expect("datatype arithmetic should still encode via numeric fallback");
        assert_eq!(encoder.solver.get_sort(term), Sort::Int);

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        // Datatype-to-numeric coercion now uses SortCoercionBridge (LOW)
        // instead of SortFallbackToInt (HIGH). The fresh constant is
        // unconstrained — conservative, not an inference failure. (#2231)
        assert_eq!(
            delta.get(&unsoundness::UnsoundnessCategory::SortCoercionBridge),
            Some(&1),
            "datatype arithmetic should use conservative SortCoercionBridge path: {delta:?}"
        );
        assert_eq!(
            delta.get(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            None,
            "datatype arithmetic should NOT use HIGH-risk SortFallbackToInt: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Bool comparison (`true >= false`) should use lossless ite(b,1,0) coercion
/// instead of creating a fresh unconstrained constant. This avoids
/// SortFallbackToInt for Rust's valid `PartialOrd for bool`. (#2558)
#[test]
#[timeout(30000)]
fn test_bool_comparison_no_sort_fallback() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        // Encode `true >= false` — both operands are Bool-sorted
        let expr = PureExpr::BinOp(
            Arc::new(bool_expr(true)),
            BinOp::Ge,
            Arc::new(bool_expr(false)),
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("Bool comparison should encode without error");

        // The result should be Bool (from the Ge comparison)
        assert_eq!(
            encoder.solver.get_sort(term),
            Sort::Bool,
            "Bool >= Bool should produce a Bool result"
        );

        // No SortFallbackToInt should have fired
        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "Bool comparison should not trigger SortFallbackToInt: {delta:?}"
        );

        // Verify the result is correct: true >= false should be provably true
        let neg = encoder.solver.not(term);
        encoder.solver.assert_term(neg);
        let result = encoder.solver.check_sat();
        assert_eq!(
            result,
            SolveResult::unsat(),
            "NOT(true >= false) should be UNSAT"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Bool-vs-Int comparison (e.g., `b < 5`) should still work — Bool is
/// coerced to Int(0/1) and the comparison proceeds normally.
#[test]
#[timeout(30000)]
fn test_bool_vs_int_comparison_no_sort_fallback() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        // Encode `true < 5`
        let expr = PureExpr::BinOp(Arc::new(bool_expr(true)), BinOp::Lt, Arc::new(int(5)));
        let term = encoder
            .encode_pure(&expr)
            .expect("Bool < Int should encode without error");
        assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "Bool vs Int comparison should not trigger SortFallbackToInt: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ═══════════════════════════════════════════════════════════════════════
// Recursive evaluation proof tests (#1135)
//
// try_evaluate_recursive produces equality axioms (fn(args) = value) that
// are asserted to the solver. A wrong result would cause false Verified.
// These functions had ZERO direct tests prior to this commit.
// ═══════════════════════════════════════════════════════════════════════

mod recursive_eval_proofs {
    use std::{collections::HashMap, sync::Arc};

    use ntest::timeout;
    use trust_wp_core::{
        formula::{BinOp, PureExpr, UnOp},
        logic::LogicFnDef,
    };

    use super::super::recursive_eval::{
        collect_concrete_logic_fn_calls, simplify_ground, try_evaluate_recursive,
    };
    use crate::tests::helpers::{binop, int, ite, var};

    fn make_logic_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
        LogicFnDef::new(
            name.to_string(),
            format!("crate::test::{name}"),
            params.into_iter().map(ToString::to_string).collect(),
            body,
        )
    }

    fn make_logic_fn_with_requires(
        name: &str,
        params: Vec<&str>,
        requires: Vec<PureExpr>,
        body: PureExpr,
    ) -> LogicFnDef {
        LogicFnDef::new_with_requires(
            name.to_string(),
            format!("crate::test::{name}"),
            params.into_iter().map(ToString::to_string).collect(),
            requires,
            body,
        )
    }

    fn make_recursive_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
        let mut lf = make_logic_fn(name, params, body);
        lf.set_is_recursive(true);
        lf
    }

    fn bool_lit(v: bool) -> PureExpr {
        PureExpr::Bool(v)
    }

    fn logic_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    /// Build the factorial body: if n <= 0 then 1 else n * fact(n - 1)
    fn factorial_body() -> PureExpr {
        ite(
            binop(var("n"), BinOp::Le, int(0)),
            int(1),
            binop(
                var("n"),
                BinOp::Mul,
                logic_call("fact", vec![binop(var("n"), BinOp::Sub, int(1))]),
            ),
        )
    }

    // ── try_evaluate_recursive ────────────────────────────────────────

    /// Non-recursive: f(x) = x + 1, f(5) → 6.
    #[test]
    #[timeout(30000)]
    fn test_eval_non_recursive_simple() {
        let f = make_logic_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        let result = try_evaluate_recursive(&logic_call("f", vec![int(5)]), &fns, 10);
        assert_eq!(result, Some(int(6)));
    }

    /// Recursive factorial: fact(4) → 24.
    #[test]
    #[timeout(30000)]
    fn test_eval_recursive_factorial() {
        let fact = make_recursive_fn("fact", vec!["n"], factorial_body());
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("fact", &fact)]);
        let result = try_evaluate_recursive(&logic_call("fact", vec![int(4)]), &fns, 10);
        assert_eq!(result, Some(int(24)));
    }

    /// Recursive base case: fact(0) → 1.
    #[test]
    #[timeout(30000)]
    fn test_eval_recursive_base_case() {
        let fact = make_recursive_fn("fact", vec!["n"], factorial_body());
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("fact", &fact)]);
        let result = try_evaluate_recursive(&logic_call("fact", vec![int(0)]), &fns, 10);
        assert_eq!(result, Some(int(1)));
    }

    /// Depth limit: fact(10) at max_depth=3 should return None.
    #[test]
    #[timeout(30000)]
    fn test_eval_depth_limit_returns_none() {
        let fact = make_recursive_fn("fact", vec!["n"], factorial_body());
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("fact", &fact)]);
        assert_eq!(
            try_evaluate_recursive(&logic_call("fact", vec![int(10)]), &fns, 3),
            None,
            "fact(10) at depth 3 should bail out"
        );
    }

    /// Unknown function returns None (no axiom asserted).
    #[test]
    #[timeout(30000)]
    fn test_eval_unknown_function_returns_none() {
        let fns: HashMap<&str, &LogicFnDef> = HashMap::new();
        assert_eq!(
            try_evaluate_recursive(&logic_call("missing", vec![int(5)]), &fns, 10),
            None
        );
    }

    /// Non-ground argument returns None (variable in arg position).
    #[test]
    #[timeout(30000)]
    fn test_eval_non_ground_arg_returns_none() {
        let f = make_logic_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        assert_eq!(
            try_evaluate_recursive(&logic_call("f", vec![var("y")]), &fns, 10),
            None
        );
    }

    /// Precondition rejection: requires(x > 0), call f(0) → None.
    #[test]
    #[timeout(30000)]
    fn test_eval_precondition_rejection() {
        let f = make_logic_fn_with_requires(
            "f",
            vec!["x"],
            vec![binop(var("x"), BinOp::Gt, int(0))],
            binop(var("x"), BinOp::Add, int(1)),
        );
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        assert_eq!(
            try_evaluate_recursive(&logic_call("f", vec![int(0)]), &fns, 10),
            None,
            "f(0) should be rejected by requires(0 > 0) = false"
        );
    }

    /// Precondition satisfied: requires(x > 0), call f(5) → 6.
    #[test]
    #[timeout(30000)]
    fn test_eval_precondition_satisfied() {
        let f = make_logic_fn_with_requires(
            "f",
            vec!["x"],
            vec![binop(var("x"), BinOp::Gt, int(0))],
            binop(var("x"), BinOp::Add, int(1)),
        );
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        assert_eq!(
            try_evaluate_recursive(&logic_call("f", vec![int(5)]), &fns, 10),
            Some(int(6))
        );
    }

    /// ITE true branch selected.
    #[test]
    #[timeout(30000)]
    fn test_eval_ite_true_branch() {
        let fns: HashMap<&str, &LogicFnDef> = HashMap::new();
        assert_eq!(
            try_evaluate_recursive(&ite(bool_lit(true), int(42), int(99)), &fns, 10),
            Some(int(42))
        );
    }

    /// ITE with non-ground condition → None.
    #[test]
    #[timeout(30000)]
    fn test_eval_ite_non_ground_condition() {
        let fns: HashMap<&str, &LogicFnDef> = HashMap::new();
        assert_eq!(
            try_evaluate_recursive(&ite(var("c"), int(1), int(2)), &fns, 10),
            None
        );
    }

    /// Cross-function: quad(x) = double(double(x)), quad(3) → 12.
    #[test]
    #[timeout(30000)]
    fn test_eval_cross_function_call() {
        let double = make_logic_fn("double", vec!["x"], binop(var("x"), BinOp::Add, var("x")));
        let quad = make_logic_fn(
            "quad",
            vec!["x"],
            logic_call("double", vec![logic_call("double", vec![var("x")])]),
        );
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("double", &double), ("quad", &quad)]);
        assert_eq!(
            try_evaluate_recursive(&logic_call("quad", vec![int(3)]), &fns, 10),
            Some(int(12))
        );
    }

    /// Bool-returning function: is_positive(5) → true.
    #[test]
    #[timeout(30000)]
    fn test_eval_bool_function() {
        let f = make_logic_fn("is_positive", vec!["x"], binop(var("x"), BinOp::Gt, int(0)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("is_positive", &f)]);
        assert_eq!(
            try_evaluate_recursive(&logic_call("is_positive", vec![int(5)]), &fns, 10),
            Some(bool_lit(true))
        );
        assert_eq!(
            try_evaluate_recursive(&logic_call("is_positive", vec![int(-3)]), &fns, 10),
            Some(bool_lit(false))
        );
    }

    // ── collect_concrete_logic_fn_calls ───────────────────────────────

    /// Collects a top-level ground call.
    #[test]
    #[timeout(30000)]
    fn test_collect_top_level_ground_call() {
        let f = make_recursive_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        let mut calls = Vec::new();
        collect_concrete_logic_fn_calls(&logic_call("f", vec![int(5)]), &fns, &mut calls);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0, "f");
        assert_eq!(calls[0].1, vec![int(5)]);
    }

    /// Filters out calls with variable arguments.
    #[test]
    #[timeout(30000)]
    fn test_collect_filters_non_ground() {
        let f = make_recursive_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        let mut calls = Vec::new();
        collect_concrete_logic_fn_calls(&logic_call("f", vec![var("y")]), &fns, &mut calls);
        assert!(calls.is_empty());
    }

    /// Mixed ground/non-ground: only ground calls collected.
    #[test]
    #[timeout(30000)]
    fn test_collect_mixed_ground_and_non_ground() {
        let f = make_recursive_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        let expr = binop(
            logic_call("f", vec![int(3)]),
            BinOp::Add,
            logic_call("f", vec![var("y")]),
        );
        let mut calls = Vec::new();
        collect_concrete_logic_fn_calls(&expr, &fns, &mut calls);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].1, vec![int(3)]);
    }

    /// Ignores functions not in the recursive_fns map.
    #[test]
    #[timeout(30000)]
    fn test_collect_ignores_unknown_fns() {
        let f = make_recursive_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        let expr = binop(
            logic_call("f", vec![int(3)]),
            BinOp::Add,
            logic_call("g", vec![int(5)]),
        );
        let mut calls = Vec::new();
        collect_concrete_logic_fn_calls(&expr, &fns, &mut calls);
        assert_eq!(calls.len(), 1, "only f should be collected");
        assert_eq!(calls[0].0, "f");
    }

    /// Traverses into quantifier bodies.
    #[test]
    #[timeout(30000)]
    fn test_collect_from_quantifier_body() {
        let f = make_recursive_fn("f", vec!["x"], binop(var("x"), BinOp::Add, int(1)));
        let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("f", &f)]);
        let expr = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(logic_call("f", vec![int(42)])),
            triggers: vec![],
        };
        let mut calls = Vec::new();
        collect_concrete_logic_fn_calls(&expr, &fns, &mut calls);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].1, vec![int(42)]);
    }

    // ── simplify_ground supplemental ──────────────────────────────────

    /// simplify_ground folds LogicFnCall arguments but preserves the call.
    #[test]
    #[timeout(30000)]
    fn test_simplify_preserves_logic_fn_call_with_folded_args() {
        let expr = logic_call("f", vec![binop(int(1), BinOp::Add, int(2))]);
        match simplify_ground(&expr) {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(name, "f");
                assert_eq!(args, vec![int(3)]);
            }
            other => panic!("Expected LogicFnCall, got: {other:?}"),
        }
    }

    /// Nested ITE with ground conditions folds completely.
    #[test]
    #[timeout(30000)]
    fn test_simplify_nested_ite_folds() {
        let inner = ite(bool_lit(true), int(42), int(99));
        let outer = ite(binop(int(1), BinOp::Gt, int(0)), inner, int(0));
        assert_eq!(simplify_ground(&outer), int(42));
    }

    /// Not(true) → false.
    #[test]
    #[timeout(30000)]
    fn test_simplify_not_true() {
        let expr = PureExpr::UnOp(UnOp::Not, Arc::new(bool_lit(true)));
        assert_eq!(simplify_ground(&expr), bool_lit(false));
    }
}

// =============================================================================
// Implies encoding tests
// =============================================================================

/// `true ==> false` should encode correctly and be satisfiable (it's false).
#[test]
#[timeout(30000)]
fn test_implies_encoding_true_implies_false() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::BinOp(
        Arc::new(bool_expr(true)),
        BinOp::Implies,
        Arc::new(bool_expr(false)),
    );
    let term = encoder.encode_pure(&expr).expect("Implies should encode");
    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);

    // true ==> false is false, so asserting it should be UNSAT
    encoder.solver.assert_term(term);
    assert_eq!(
        encoder.solver.check_sat(),
        SolveResult::unsat(),
        "true ==> false is false, asserting it should be UNSAT"
    );
}

/// `false ==> false` should be true (vacuously).
#[test]
#[timeout(30000)]
fn test_implies_encoding_false_implies_false() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::BinOp(
        Arc::new(bool_expr(false)),
        BinOp::Implies,
        Arc::new(bool_expr(false)),
    );
    let term = encoder.encode_pure(&expr).expect("Implies should encode");

    // false ==> false is true, so NOT(false ==> false) should be UNSAT
    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);
    assert_eq!(
        encoder.solver.check_sat(),
        SolveResult::unsat(),
        "NOT(false ==> false) should be UNSAT — vacuously true"
    );
}

/// `x ==> x` should be a tautology for any Bool x.
#[test]
#[timeout(30000)]
fn test_implies_encoding_reflexive_tautology() {
    let mut encoder = AYEncoder::new();
    let x = var_with_sort("x", ExprSort::Bool);
    let expr = PureExpr::BinOp(Arc::new(x.clone()), BinOp::Implies, Arc::new(x));
    let term = encoder.encode_pure(&expr).expect("Implies should encode");

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);
    assert_eq!(
        encoder.solver.check_sat(),
        SolveResult::unsat(),
        "NOT(x ==> x) should be UNSAT — reflexive implication is a tautology"
    );
}

// =============================================================================
// Bool-to-Int coercion in bitwise operators
// =============================================================================

/// `true & false` (BitAnd on Bool operands) should coerce Bools to Int
/// via ite(b,1,0) and produce an Int result.
#[test]
#[timeout(30000)]
fn test_bool_bitand_coerces_to_int() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        let mut encoder = AYEncoder::new();
        let expr = PureExpr::BinOp(
            Arc::new(bool_expr(true)),
            BinOp::BitAnd,
            Arc::new(bool_expr(false)),
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("Bool BitAnd should encode");

        // Bitwise ops use IntOnly mode, result should be Int
        assert_eq!(
            encoder.solver.get_sort(term),
            Sort::Int,
            "Bool BitAnd should produce Int result after coercion"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// `true | false` (BitOr on Bool operands) should encode and produce 1.
#[test]
#[timeout(30000)]
fn test_bool_bitor_coerces_to_int() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        let mut encoder = AYEncoder::new();
        let expr = PureExpr::BinOp(
            Arc::new(bool_expr(true)),
            BinOp::BitOr,
            Arc::new(bool_expr(false)),
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("Bool BitOr should encode");
        assert_eq!(encoder.solver.get_sort(term), Sort::Int);

        // true | false = 1 | 0 = 1, so term != 1 should be UNSAT
        let one = encoder.solver.int_const(1);
        let neq = encoder.solver.neq(term, one);
        encoder.solver.assert_term(neq);
        assert_eq!(
            encoder.solver.check_sat(),
            SolveResult::unsat(),
            "true | false should equal 1 after Bool-to-Int coercion"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Bool XOR: `true ^ false` should produce 1.
#[test]
#[timeout(30000)]
fn test_bool_bitxor_coerces_to_int() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        let mut encoder = AYEncoder::new();
        let expr = PureExpr::BinOp(
            Arc::new(bool_expr(true)),
            BinOp::BitXor,
            Arc::new(bool_expr(false)),
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("Bool BitXor should encode");
        assert_eq!(encoder.solver.get_sort(term), Sort::Int);

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// =============================================================================
// Bitwise proof mode — native BV theory encoding (#2666)
// =============================================================================

/// In bitwise proof mode, BitAnd uses ay's native bvand via Int↔BV conversion.
/// Verify: 0xFF & 0x0F = 0x0F (255 & 15 = 15).
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_bvand_exact() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        encoder.set_bitwise_proof_mode(true);

        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Int(0xFF)),
            BinOp::BitAnd,
            Arc::new(PureExpr::Int(0x0F)),
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("BitAnd in BV mode should encode");

        // Result should be Int (after bv2int conversion)
        assert_eq!(encoder.solver.get_sort(term), Sort::Int);

        // 0xFF & 0x0F = 0x0F = 15
        let expected = encoder.solver.int_const(15);
        let neq = encoder.solver.neq(term, expected);
        encoder.solver.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "0xFF & 0x0F should equal 15 in BV mode"
        );

        // BitwiseUfApproximation should NOT fire in BV mode
        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::BitwiseUfApproximation),
            "BV mode should not fire BitwiseUfApproximation: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// In bitwise proof mode, BitOr uses ay's native bvor.
/// Verify: 0xF0 | 0x0F = 0xFF (240 | 15 = 255).
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_bvor_exact() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0xF0)),
        BinOp::BitOr,
        Arc::new(PureExpr::Int(0x0F)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("BitOr in BV mode should encode");

    let expected = encoder.solver.int_const(255);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "0xF0 | 0x0F should equal 255 in BV mode"
    );
}

/// In bitwise proof mode, BitXor uses ay's native bvxor.
/// Verify: 0xFF ^ 0xFF = 0 (self-inverse property, now exact).
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_bvxor_self_inverse() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0xFF)),
        BinOp::BitXor,
        Arc::new(PureExpr::Int(0xFF)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("BitXor in BV mode should encode");

    let zero = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(term, zero);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "0xFF ^ 0xFF should equal 0 in BV mode"
    );
}

/// In bitwise proof mode, Shl uses ay's native bvshl.
/// Verify: 1 << 4 = 16.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_shl_exact() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(1)),
        BinOp::Shl,
        Arc::new(PureExpr::Int(4)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("Shl in BV mode should encode");

    let expected = encoder.solver.int_const(16);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "1 << 4 should equal 16 in BV mode"
    );
}

/// In bitwise proof mode, Shr uses ay's native bvlshr (logical shift right).
/// Verify: 16 >> 2 = 4.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_shr_exact() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(16)),
        BinOp::Shr,
        Arc::new(PureExpr::Int(2)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("Shr in BV mode should encode");

    let expected = encoder.solver.int_const(4);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "16 >> 2 should equal 4 in BV mode"
    );
}

/// In bitwise proof mode, no BV operation should fire BitwiseUfApproximation.
/// Tests all 5 operations (AND, OR, XOR, SHL, SHR) in a single encoder.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_no_unsoundness_all_ops() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();
        encoder.set_bitwise_proof_mode(true);

        let ops = [
            BinOp::BitAnd,
            BinOp::BitOr,
            BinOp::BitXor,
            BinOp::Shl,
            BinOp::Shr,
        ];
        for op in ops {
            let expr = PureExpr::BinOp(Arc::new(PureExpr::Int(42)), op, Arc::new(PureExpr::Int(7)));
            encoder
                .encode_pure(&expr)
                .expect("BV mode op should encode");
        }

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::BitwiseUfApproximation),
            "BV mode should not fire BitwiseUfApproximation for any op: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// BV identity: `(a & b) | (a ^ b) == (a | b)`.
///
/// This is a fundamental bitvector identity that should hold exactly in BV
/// mode. In UF mode this would not be provable since UFs don't encode
/// bit-level relationships between operations.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_bv_identity_and_xor_or() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let a = PureExpr::Int(0xAB);
    let b = PureExpr::Int(0xCD);

    // (a & b)
    let a_and_b = PureExpr::BinOp(Arc::new(a.clone()), BinOp::BitAnd, Arc::new(b.clone()));
    // (a ^ b)
    let a_xor_b = PureExpr::BinOp(Arc::new(a.clone()), BinOp::BitXor, Arc::new(b.clone()));
    // (a & b) | (a ^ b)
    let lhs = PureExpr::BinOp(Arc::new(a_and_b), BinOp::BitOr, Arc::new(a_xor_b));
    // (a | b)
    let rhs = PureExpr::BinOp(Arc::new(a), BinOp::BitOr, Arc::new(b));

    let lhs_term = encoder.encode_pure(&lhs).expect("lhs should encode");
    let rhs_term = encoder.encode_pure(&rhs).expect("rhs should encode");

    let neq = encoder.solver.neq(lhs_term, rhs_term);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "(a & b) | (a ^ b) should equal (a | b) in BV mode"
    );
}

/// BV shift: `1 << 32` should produce 2^32 in 64-bit BV mode.
/// This validates that the Int-to-BV round-trip works for multi-word shifts.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_shl_large_shift() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(1)),
        BinOp::Shl,
        Arc::new(PureExpr::Int(32)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("Shl in BV mode should encode");

    // 1 << 32 = 2^32 = 4294967296
    let expected = encoder.solver.int_const(4_294_967_296_i64);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "1 << 32 should equal 2^32 in BV mode"
    );
}

/// BV xor identity: `x ^ 0 == x` should hold exactly for any value.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_bvxor_zero_identity() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0xDEAD_BEEF_i64)),
        BinOp::BitXor,
        Arc::new(PureExpr::Int(0)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("BitXor in BV mode should encode");

    let expected = encoder.solver.int_const(0xDEAD_BEEF_i64);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x ^ 0 should equal x in BV mode"
    );
}

/// BV and zero: `x & 0 == 0` should hold exactly.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_bvand_zero_annihilation() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0xFFFF_FFFF_i64)),
        BinOp::BitAnd,
        Arc::new(PureExpr::Int(0)),
    );
    let term = encoder
        .encode_pure(&expr)
        .expect("BitAnd in BV mode should encode");

    let expected = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x & 0 should equal 0 in BV mode"
    );
}

// =============================================================================
// Bitwise proof mode — symbolic variable tests (#2666)
//
// BV mode converts Int operands to BV(64) via `int2bv`, applies native BV
// operations, and converts back via `bv2int`. For concrete values this
// gives exact bit-level semantics (proven by tests above).
//
// For symbolic variables, ay-dpll's BV theory can prove some properties
// (e.g., `x ^ x == 0`) but not all algebraic BV identities through the
// Int→BV→Int round-trip. This is a ay-level limitation, not an encoding
// bug: the `int2bv`/`bv2int` conversion creates complex constraints that
// ay-dpll's BV solver does not fully simplify for symbolic inputs.
//
// These tests verify that:
// 1. Symbolic BV operations encode without errors
// 2. Properties that ay CAN prove symbolically are verified (XOR self-zero)
// 3. Properties that ay CANNOT yet prove return Unknown (not false proofs)
// 4. BV mode proves bit-level properties on concrete values that UF cannot
// =============================================================================

/// BV mode: `x ^ x == 0` for any symbolic x (self-inverse of XOR).
///
/// This works because `int2bv(x) ^ int2bv(x) == BV(0)` and
/// `bv2int(BV(0)) == 0` regardless of the Int→BV truncation.
/// ay-dpll can simplify this because `bvxor(t, t)` reduces to zero
/// at the term level.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_symbolic_xor_self_zero() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let x = var_with_sort("sym_x", ExprSort::Int);
    let expr = PureExpr::BinOp(Arc::new(x.clone()), BinOp::BitXor, Arc::new(x));
    let xor_term = encoder
        .encode_pure(&expr)
        .expect("BitXor(sym_x, sym_x) should encode in BV mode");

    let zero = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(xor_term, zero);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x ^ x should equal 0 for any symbolic x in BV mode"
    );
}

/// BV mode: `(x & single_bit_mask) == 0` in a Boolean condition should avoid
/// converting the masked result back through Int arithmetic. This is the shape
/// emitted by the popcount specs (`n & 0x80 == 0`) and is encoded as an Int
/// low-bit test so logic-function body axioms do not contain native BV extract.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_symbolic_single_bit_mask_zero_condition_uses_int_low_bit_test() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let n = var_with_sort("pop_n", ExprSort::Int);
    let masked = PureExpr::BinOp(Arc::new(n), BinOp::BitAnd, Arc::new(int(0x80)));
    let expr = eq(masked, int(0));
    let encoded = encoder
        .encode_pure(&expr)
        .expect("single-bit mask zero comparison should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let n_term = encoder.get_or_declare_var("pop_n", Sort::Int).unwrap();
    let period = encoder.solver.int_const(0x100);
    let low_bits = encoder.solver.modulo(n_term, period);
    let mask = encoder.solver.int_const(0x80);
    let expected = encoder.solver.lt(low_bits, mask);
    let differs = encoder.solver.neq(encoded, expected);
    encoder.solver.assert_term(differs);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "single-bit mask zero comparison should match the Int low-bit test; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_symbolic_single_bit_mask_nonzero_condition_uses_int_low_bit_test() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let n = var_with_sort("pop_n", ExprSort::Int);
    let masked = PureExpr::BinOp(Arc::new(n), BinOp::BitAnd, Arc::new(int(0x40)));
    let expr = ne(masked, int(0));
    let encoded = encoder
        .encode_pure(&expr)
        .expect("single-bit mask nonzero comparison should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let n_term = encoder.get_or_declare_var("pop_n", Sort::Int).unwrap();
    let period = encoder.solver.int_const(0x80);
    let low_bits = encoder.solver.modulo(n_term, period);
    let mask = encoder.solver.int_const(0x40);
    let expected = encoder.solver.ge(low_bits, mask);
    let differs = encoder.solver.neq(encoded, expected);
    encoder.solver.assert_term(differs);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "single-bit mask nonzero comparison should match the Int low-bit test; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_or_bit_test_splits_to_propositional_disjunction() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let lhs = var_with_sort("bits_lhs", ExprSort::Int);
    let rhs = var_with_sort("bits_rhs", ExprSort::Int);
    let b = var_with_sort("bits_b", ExprSort::Int);
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(b.clone()));
    let lhs_masked = PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::BitAnd, Arc::new(mask.clone()));
    let lhs_has_bit = ne(lhs_masked, int(0));
    let merged = PureExpr::BinOp(Arc::new(lhs), BinOp::BitOr, Arc::new(rhs));
    let merged_masked = PureExpr::BinOp(Arc::new(merged), BinOp::BitAnd, Arc::new(mask));
    let merged_has_bit = ne(merged_masked, int(0));
    let expr = PureExpr::BinOp(
        Arc::new(lhs_has_bit),
        BinOp::Implies,
        Arc::new(merged_has_bit),
    );
    let encoded = encoder
        .encode_pure(&expr)
        .expect("OR bit-test implication should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "has_bit(lhs, b) should imply has_bit(lhs | rhs, b) propositionally; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_result_alias_or_bit_test_splits_to_propositional_disjunction() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let lhs = var_with_sort("bits_alias_lhs", ExprSort::Int);
    let rhs = var_with_sort("bits_alias_rhs", ExprSort::Int);
    let b = var_with_sort("bits_alias_b", ExprSort::Int);
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(b.clone()));
    let merged = PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::BitOr, Arc::new(rhs));

    let merged_term = encoder
        .encode_pure(&merged)
        .expect("merged OR expression should encode before rebinding result");
    encoder.rebind_var("bits_alias_result", merged_term, Sort::Int);
    encoder.record_var_expr_alias("bits_alias_result", merged);

    let lhs_masked = PureExpr::BinOp(Arc::new(lhs), BinOp::BitAnd, Arc::new(mask.clone()));
    let lhs_has_bit = ne(lhs_masked, int(0));
    let result = var_with_sort("bits_alias_result", ExprSort::Int);
    let result_masked = PureExpr::BinOp(Arc::new(result), BinOp::BitAnd, Arc::new(mask));
    let result_has_bit = ne(result_masked, int(0));
    let expr = PureExpr::BinOp(
        Arc::new(lhs_has_bit),
        BinOp::Implies,
        Arc::new(result_has_bit),
    );
    let encoded = encoder
        .encode_pure(&expr)
        .expect("result-alias OR bit-test implication should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "has_bit(lhs, b) should imply has_bit(result, b) when result aliases lhs | rhs; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_result_alias_or_bit_test_peels_value_context_wrappers() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let lhs = var_with_sort("bits_wrapped_alias_lhs", ExprSort::Int);
    let rhs = var_with_sort("bits_wrapped_alias_rhs", ExprSort::Int);
    let b = var_with_sort("bits_wrapped_alias_b", ExprSort::Int);
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(b.clone()));
    let merged = PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::BitOr, Arc::new(rhs));
    let wrapped = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(b.clone()),
            BinOp::Lt,
            Arc::new(int(64)),
        )),
        body: Arc::new(PureExpr::LetObligation {
            obligation: Arc::new(bool_expr(true)),
            body: Arc::new(merged),
        }),
    };

    let wrapped_term = encoder
        .encode_pure(&wrapped)
        .expect("wrapped OR expression should encode before rebinding result");
    encoder.rebind_var("bits_wrapped_alias_result", wrapped_term, Sort::Int);
    encoder.record_var_expr_alias("bits_wrapped_alias_result", wrapped);

    let lhs_masked = PureExpr::BinOp(Arc::new(lhs), BinOp::BitAnd, Arc::new(mask.clone()));
    let lhs_has_bit = ne(lhs_masked, int(0));
    let result = var_with_sort("bits_wrapped_alias_result", ExprSort::Int);
    let result_masked = PureExpr::BinOp(Arc::new(result), BinOp::BitAnd, Arc::new(mask));
    let result_has_bit = ne(result_masked, int(0));
    let expr = PureExpr::BinOp(
        Arc::new(lhs_has_bit),
        BinOp::Implies,
        Arc::new(result_has_bit),
    );
    let encoded = encoder
        .encode_pure(&expr)
        .expect("wrapped result-alias OR bit-test implication should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "has_bit(lhs, b) should imply has_bit(result, b) when result aliases wrapped lhs | rhs; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_wrapped_or_alias_proves_inserted_symbolic_bit() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);
    register_single_bit_test_logic_fn(&mut encoder, "has_bit_for_wrapped_inserted_bit");

    let bitvec = var_with_sort("bits_inserted_bitvec", ExprSort::Int);
    let bit = var_with_sort("bits_inserted_bit", ExprSort::Int);
    let result = var_with_sort("bits_inserted_result", ExprSort::Int);
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(bit.clone()));
    let merged = PureExpr::BinOp(Arc::new(bitvec), BinOp::BitOr, Arc::new(mask));
    let bit_nonnegative = PureExpr::BinOp(Arc::new(int(0)), BinOp::Le, Arc::new(bit.clone()));
    let bit_in_width = PureExpr::BinOp(Arc::new(bit.clone()), BinOp::Lt, Arc::new(int(64)));
    let wrapped = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(bit_nonnegative),
            BinOp::And,
            Arc::new(bit_in_width),
        )),
        body: Arc::new(merged),
    };

    let wrapped_term = encoder
        .encode_pure(&wrapped)
        .expect("wrapped set-bit expression should encode before rebinding result");
    encoder.rebind_var("bits_inserted_result", wrapped_term, Sort::Int);
    encoder.record_var_expr_alias("bits_inserted_result", wrapped);

    let result_has_bit = logic_call_expr("has_bit_for_wrapped_inserted_bit", vec![result, bit]);
    let encoded = encoder
        .encode_pure(&result_has_bit)
        .expect("wrapped set-bit postcondition should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set_bit-style result alias should prove has_bit(result, bit); got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_clear_bit_alias_proves_cleared_symbolic_bit() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);
    register_single_bit_test_logic_fn(&mut encoder, "has_bit_for_clear_alias_absent");

    let bitvec = var_with_sort("bits_clear_bitvec", ExprSort::Int);
    let bit = var_with_sort("bits_clear_bit", ExprSort::Int);
    let result = var_with_sort("bits_clear_result", ExprSort::Int);
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(bit.clone()));
    let cleared = PureExpr::BinOp(
        Arc::new(bitvec),
        BinOp::BitAnd,
        Arc::new(PureExpr::UnOp(UnOp::BitNot, Arc::new(mask))),
    );
    let bit_nonnegative = PureExpr::BinOp(Arc::new(int(0)), BinOp::Le, Arc::new(bit.clone()));
    let bit_in_width = PureExpr::BinOp(Arc::new(bit.clone()), BinOp::Lt, Arc::new(int(64)));
    let wrapped = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(bit_nonnegative),
            BinOp::And,
            Arc::new(bit_in_width),
        )),
        body: Arc::new(cleared),
    };

    let wrapped_term = encoder
        .encode_pure(&wrapped)
        .expect("wrapped clear-bit expression should encode before rebinding result");
    encoder.rebind_var("bits_clear_result", wrapped_term, Sort::Int);
    encoder.record_var_expr_alias("bits_clear_result", wrapped);

    let result_has_bit = logic_call_expr("has_bit_for_clear_alias_absent", vec![result, bit]);
    let encoded = encoder
        .encode_pure(&result_has_bit)
        .expect("clear-bit absence postcondition should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    encoder.solver.assert_term(encoded);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "clear-bit result alias should prove cleared bit absent; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_clear_bit_alias_preserves_other_symbolic_bits() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);
    register_single_bit_test_logic_fn(&mut encoder, "has_bit_for_clear_alias_preserve");

    let bitvec = var_with_sort("bits_clear_keep_bitvec", ExprSort::Int);
    let bit = var_with_sort("bits_clear_keep_bit", ExprSort::Int);
    let b = var_with_sort("bits_clear_keep_b", ExprSort::Int);
    let result = var_with_sort("bits_clear_keep_result", ExprSort::Int);
    let mask = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(bit.clone()));
    let cleared = PureExpr::BinOp(
        Arc::new(bitvec.clone()),
        BinOp::BitAnd,
        Arc::new(PureExpr::UnOp(UnOp::BitNot, Arc::new(mask))),
    );
    let bit_nonnegative = PureExpr::BinOp(Arc::new(int(0)), BinOp::Le, Arc::new(bit.clone()));
    let bit_in_width = PureExpr::BinOp(Arc::new(bit.clone()), BinOp::Lt, Arc::new(int(64)));
    let wrapped = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(bit_nonnegative),
            BinOp::And,
            Arc::new(bit_in_width),
        )),
        body: Arc::new(cleared),
    };

    let wrapped_term = encoder
        .encode_pure(&wrapped)
        .expect("wrapped clear-bit expression should encode before rebinding result");
    encoder.rebind_var("bits_clear_keep_result", wrapped_term, Sort::Int);
    encoder.record_var_expr_alias("bits_clear_keep_result", wrapped);

    let b_differs = ne(b.clone(), bit);
    let original_has_bit =
        logic_call_expr("has_bit_for_clear_alias_preserve", vec![bitvec, b.clone()]);
    let result_has_bit = logic_call_expr("has_bit_for_clear_alias_preserve", vec![result, b]);
    let premise = PureExpr::BinOp(Arc::new(b_differs), BinOp::And, Arc::new(original_has_bit));
    let expr = implies(premise, result_has_bit);
    let encoded = encoder
        .encode_pure(&expr)
        .expect("clear-bit preservation implication should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "clear-bit alias should preserve other set bits; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_expands_single_bit_logic_call_for_or_alias() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);
    register_single_bit_test_logic_fn(&mut encoder, "has_bit_for_or_alias");

    let lhs = var_with_sort("logic_bits_lhs", ExprSort::Int);
    let rhs = var_with_sort("logic_bits_rhs", ExprSort::Int);
    let b = var_with_sort("logic_bits_b", ExprSort::Int);
    let result = var_with_sort("logic_bits_result", ExprSort::Int);
    let merged = PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::BitOr, Arc::new(rhs));

    let merged_term = encoder
        .encode_pure(&merged)
        .expect("merged OR expression should encode before rebinding result");
    encoder.rebind_var("logic_bits_result", merged_term, Sort::Int);
    encoder.record_var_expr_alias("logic_bits_result", merged);

    let lhs_has_bit = logic_call_expr("has_bit_for_or_alias", vec![lhs, b.clone()]);
    let result_has_bit = logic_call_expr("has_bit_for_or_alias", vec![result, b]);
    let expr = PureExpr::BinOp(
        Arc::new(lhs_has_bit),
        BinOp::Implies,
        Arc::new(result_has_bit),
    );
    let encoded = encoder
        .encode_pure(&expr)
        .expect("expanded single-bit logic implication should encode");
    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);

    let negated = encoder.solver.not(encoded);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "expanded has_bit(lhs, b) should imply has_bit(result, b) when result aliases lhs | rhs; got {result:?}"
    );
}

/// BV mode symbolic encoding does not produce false proofs (soundness).
///
/// For a symbolic `x & y` in BV mode, asserting the result equals a
/// specific concrete value should be Sat (since there exist x, y that
/// satisfy it).
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_symbolic_no_false_proof() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let x = var_with_sort("sym_x", ExprSort::Int);
    let y = var_with_sort("sym_y", ExprSort::Int);

    let expr = PureExpr::BinOp(Arc::new(x), BinOp::BitAnd, Arc::new(y));
    let and_term = encoder
        .encode_pure(&expr)
        .expect("BitAnd(sym_x, sym_y) should encode in BV mode");

    // Assert result == 15: there exist x, y such that x & y == 15
    // (e.g., x = 0xFF, y = 0x0F). This should be Sat.
    let fifteen = encoder.solver.int_const(15);
    let eq = encoder.eq_term(and_term, fifteen);
    encoder.solver.assert_term(eq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "x & y == 15 should be Sat in BV mode; got {result:?}"
    );
}

/// BV mode proves concrete multi-operation identity that UF mode cannot.
///
/// `(0xAA & 0xFF) | (0xAA ^ 0xFF)` == `0xFF`. This requires understanding
/// the relationship between AND, XOR, and OR at the bit level. UF mode
/// treats each operation independently and cannot derive this.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_concrete_cross_op_identity() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let aa = PureExpr::Int(0xAA);
    let ff = PureExpr::Int(0xFF);

    // (0xAA & 0xFF) = 0xAA
    let and_part = PureExpr::BinOp(Arc::new(aa.clone()), BinOp::BitAnd, Arc::new(ff.clone()));
    // (0xAA ^ 0xFF) = 0x55
    let xor_part = PureExpr::BinOp(Arc::new(aa), BinOp::BitXor, Arc::new(ff));
    // (0xAA & 0xFF) | (0xAA ^ 0xFF) = 0xAA | 0x55 = 0xFF
    let combined = PureExpr::BinOp(Arc::new(and_part), BinOp::BitOr, Arc::new(xor_part));

    let term = encoder
        .encode_pure(&combined)
        .expect("cross-op expression should encode");

    let expected = encoder.solver.int_const(0xFF);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "(0xAA & 0xFF) | (0xAA ^ 0xFF) should equal 0xFF in BV mode"
    );
}

/// BV mode: concrete bit-masking with shift produces exact result.
///
/// `(1 << 8) - 1` is not directly a bitwise operation, but
/// `0xFFFF & 0x00FF == 0x00FF` verifies mask extraction works.
/// This validates the interaction of AND with concrete masks.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_concrete_mask_extraction() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    // 0xDEAD_BEEF & 0x0000_FFFF = 0x0000_BEEF
    let value = PureExpr::Int(0xDEAD_BEEF_i64);
    let mask = PureExpr::Int(0x0000_FFFF);
    let masked = PureExpr::BinOp(Arc::new(value), BinOp::BitAnd, Arc::new(mask));

    let term = encoder
        .encode_pure(&masked)
        .expect("mask extraction should encode");

    let expected = encoder.solver.int_const(0xBEEF);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "0xDEAD_BEEF & 0x0000_FFFF should equal 0xBEEF in BV mode"
    );
}

/// BV mode: concrete shift-and-mask round-trip.
///
/// `(0xABCD << 16) >> 16 == 0xABCD` — shift left then right by the same
/// amount should recover the original value (for values that fit in 48 bits).
/// This demonstrates precise shift semantics in BV mode.
#[test]
#[timeout(30000)]
fn test_bitwise_proof_mode_concrete_shift_roundtrip() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(true);

    let value = PureExpr::Int(0xABCD);
    let sixteen = PureExpr::Int(16);

    // (0xABCD << 16)
    let shifted_left = PureExpr::BinOp(Arc::new(value), BinOp::Shl, Arc::new(sixteen.clone()));
    // (0xABCD << 16) >> 16
    let shifted_back = PureExpr::BinOp(Arc::new(shifted_left), BinOp::Shr, Arc::new(sixteen));

    let term = encoder
        .encode_pure(&shifted_back)
        .expect("shift round-trip should encode");

    let expected = encoder.solver.int_const(0xABCD);
    let neq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "(0xABCD << 16) >> 16 should equal 0xABCD in BV mode"
    );
}

// =============================================================================
// UF bound axioms — non-negativity and monotonicity properties (#2666)
//
// These tests verify the legacy UF axiom path. Since #2666, BV mode is on
// by default, so these tests explicitly disable it to exercise the UF path.
// =============================================================================

/// Helper: assert x >= 0 and y >= 0 for two variables, working around borrow splits.
fn assert_both_nonneg(encoder: &mut AYEncoder, x_name: &str, y_name: &str) {
    let x_term = encoder.get_or_declare_var(x_name, Sort::Int).unwrap();
    let zero = encoder.solver.int_const(0);
    let x_nonneg = encoder.solver.ge(x_term, zero);
    encoder.solver.assert_term(x_nonneg);

    let y_term = encoder.get_or_declare_var(y_name, Sort::Int).unwrap();
    let zero = encoder.solver.int_const(0);
    let y_nonneg = encoder.solver.ge(y_term, zero);
    encoder.solver.assert_term(y_nonneg);
}

/// UF axiom: `x >= 0 /\ y >= 0 => (x & y) >= 0`
/// Bitwise AND of non-negative integers is non-negative.
#[test]
#[timeout(30000)]
fn test_uf_bitand_nonneg_result() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test UF axiom path
    let x = var_with_sort("x", ExprSort::Int);
    let y = var_with_sort("y", ExprSort::Int);

    // Encode x & y (UF mode, not BV mode)
    let expr = PureExpr::BinOp(Arc::new(x), BinOp::BitAnd, Arc::new(y));
    let term = encoder.encode_pure(&expr).expect("BitAnd should encode");

    assert_both_nonneg(&mut encoder, "x", "y");

    // Assert result < 0 — should be UNSAT given the axiom
    let zero = encoder.solver.int_const(0);
    let result_neg = encoder.solver.lt(term, zero);
    encoder.solver.assert_term(result_neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x & y should be non-negative when x >= 0, y >= 0 (UF axiom #2666)"
    );
}

/// UF axiom: `x >= 0 /\ y >= 0 => (x & y) <= x`
/// Bitwise AND can only clear bits, so result <= either operand.
#[test]
#[timeout(30000)]
fn test_uf_bitand_le_operand() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test UF axiom path
    let x = var_with_sort("x", ExprSort::Int);
    let y = var_with_sort("y", ExprSort::Int);

    let expr = PureExpr::BinOp(Arc::new(x), BinOp::BitAnd, Arc::new(y));
    let term = encoder.encode_pure(&expr).expect("BitAnd should encode");

    assert_both_nonneg(&mut encoder, "x", "y");

    // Assert result > x — should be UNSAT (AND cannot increase value)
    let x_term = encoder.get_or_declare_var("x", Sort::Int).unwrap();
    let result_gt_x = encoder.solver.gt(term, x_term);
    encoder.solver.assert_term(result_gt_x);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x & y should be <= x when both non-negative (UF axiom #2666)"
    );
}

/// UF axiom: `x >= 0 /\ y >= 0 => (x | y) >= x`
/// Bitwise OR can only set bits, so result >= either operand.
#[test]
#[timeout(30000)]
fn test_uf_bitor_ge_operand() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test UF axiom path
    let x = var_with_sort("x", ExprSort::Int);
    let y = var_with_sort("y", ExprSort::Int);

    let expr = PureExpr::BinOp(Arc::new(x), BinOp::BitOr, Arc::new(y));
    let term = encoder.encode_pure(&expr).expect("BitOr should encode");

    assert_both_nonneg(&mut encoder, "x", "y");

    // Assert result < x — should be UNSAT (OR cannot decrease value)
    let x_term = encoder.get_or_declare_var("x", Sort::Int).unwrap();
    let result_lt_x = encoder.solver.lt(term, x_term);
    encoder.solver.assert_term(result_lt_x);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x | y should be >= x when both non-negative (UF axiom #2666)"
    );
}

/// UF axiom: `x >= 0 /\ y >= 0 => (x ^ y) >= 0`
/// Bitwise XOR of non-negative integers is non-negative.
#[test]
#[timeout(30000)]
fn test_uf_bitxor_nonneg_result() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test UF axiom path
    let x = var_with_sort("x", ExprSort::Int);
    let y = var_with_sort("y", ExprSort::Int);

    let expr = PureExpr::BinOp(Arc::new(x), BinOp::BitXor, Arc::new(y));
    let term = encoder.encode_pure(&expr).expect("BitXor should encode");

    assert_both_nonneg(&mut encoder, "x", "y");

    let zero = encoder.solver.int_const(0);
    let result_neg = encoder.solver.lt(term, zero);
    encoder.solver.assert_term(result_neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x ^ y should be non-negative when x >= 0, y >= 0 (UF axiom #2666)"
    );
}

/// UF axiom: `x >= 0 /\ y >= 0 => (x >> y) <= x`
/// Right shift can only shrink the value for non-negative inputs.
#[test]
#[timeout(30000)]
fn test_uf_shr_le_operand() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test UF axiom path
    let x = var_with_sort("x", ExprSort::Int);
    let y = var_with_sort("y", ExprSort::Int);

    let expr = PureExpr::BinOp(Arc::new(x), BinOp::Shr, Arc::new(y));
    let term = encoder.encode_pure(&expr).expect("Shr should encode");

    assert_both_nonneg(&mut encoder, "x", "y");

    // Assert result > x — should be UNSAT (right shift cannot increase value)
    let x_term = encoder.get_or_declare_var("x", Sort::Int).unwrap();
    let result_gt_x = encoder.solver.gt(term, x_term);
    encoder.solver.assert_term(result_gt_x);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x >> y should be <= x when both non-negative (UF axiom #2666)"
    );
}

/// `select_structural_sort_target` should prefer native Seq over Datatype(Vec).
/// Datatype(Vec) comes from struct layout extraction but the canonical encoding
/// sort for collections is Sort::Seq(Int) post-#2080. (#2699)
#[test]
#[timeout(30000)]
fn test_select_structural_sort_target_seq_vs_datatype_vec() {
    use ay_dpll::api::DatatypeSort;

    let seq = Sort::seq(Sort::Int);
    let dt_vec = Sort::Datatype(DatatypeSort {
        name: "Vec".to_string(),
        constructors: vec![],
    });

    let result = super::select_structural_sort_target(&seq, &dt_vec);
    assert_eq!(
        result,
        Some(Sort::seq(Sort::Int)),
        "Seq(Int) vs Datatype(Vec) should prefer Seq(Int), got {result:?}"
    );

    // Also test reversed order
    let result_rev = super::select_structural_sort_target(&dt_vec, &seq);
    assert_eq!(
        result_rev,
        Some(Sort::seq(Sort::Int)),
        "Datatype(Vec) vs Seq(Int) should prefer Seq(Int), got {result_rev:?}"
    );
}

/// `safe_ite` should harmonize mismatched sorts without panicking. (#2699)
#[test]
#[timeout(30000)]
fn test_safe_ite_harmonizes_option_vs_option_int() {
    let mut encoder = AYEncoder::new();
    let cond = encoder.solver.bool_const(true);
    let opt_int_sort = Sort::Uninterpreted("OptionInt".to_string());
    let opt_sort = Sort::Uninterpreted("Option".to_string());
    let then_term = encoder
        .solver
        .declare_const("then_val", opt_int_sort.clone());
    let else_term = encoder.solver.declare_const("else_val", opt_sort);

    // This previously could panic with "Ite branch sort mismatch".
    // safe_ite should harmonize and succeed.
    let result = encoder.safe_ite(cond, then_term, else_term);
    let result_sort = encoder.solver.get_sort(result);

    // Result should not be Bool (that would indicate fallback failure)
    assert_ne!(
        result_sort,
        Sort::Bool,
        "safe_ite result should not be Bool"
    );
}

/// `safe_ite` on already-matching sorts should pass through directly. (#2699)
#[test]
#[timeout(30000)]
fn test_safe_ite_matching_sorts_passes_through() {
    let mut encoder = AYEncoder::new();
    let cond = encoder.solver.bool_const(true);
    let a = encoder.solver.int_const(42);
    let b = encoder.solver.int_const(17);

    let result = encoder.safe_ite(cond, a, b);
    assert_eq!(
        encoder.solver.get_sort(result),
        Sort::Int,
        "safe_ite with matching Int sorts should produce Int"
    );
}

/// UF axiom: `x >= 0 /\ y >= 0 => (x << y) >= x`
/// Left shift can only grow the value for non-negative inputs.
#[test]
#[timeout(30000)]
fn test_uf_shl_ge_operand() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test UF axiom path
    let x = var_with_sort("x", ExprSort::Int);
    let y = var_with_sort("y", ExprSort::Int);

    let expr = PureExpr::BinOp(Arc::new(x), BinOp::Shl, Arc::new(y));
    let term = encoder.encode_pure(&expr).expect("Shl should encode");

    assert_both_nonneg(&mut encoder, "x", "y");

    // Assert result < x — should be UNSAT (left shift cannot decrease value)
    let x_term = encoder.get_or_declare_var("x", Sort::Int).unwrap();
    let result_lt_x = encoder.solver.lt(term, x_term);
    encoder.solver.assert_term(result_lt_x);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x << y should be >= x when both non-negative (UF axiom #2666)"
    );
}

// === Seq-family bridging in harmonize_eq_or_ite_terms (#2699) ===

/// When one ITE branch is Seq(Int) and the other is Uninterpreted("Vec"),
/// `harmonize_eq_or_ite_terms` should bridge the Vec term to Seq via
/// `coerce_to_seq` (preserving the value via UF bridge with injectivity)
/// instead of creating a fresh unconstrained constant. (#2699)
#[test]
#[timeout(30000)]
fn test_harmonize_seq_vs_uninterpreted_vec_bridges_to_seq() {
    let mut encoder = AYEncoder::new();
    let seq_term = encoder
        .solver
        .declare_const("seq_val", Sort::seq(Sort::Int));
    let vec_sort = Sort::Uninterpreted("Vec".to_string());
    let vec_term = encoder.solver.declare_const("vec_val", vec_sort);

    let (a, b) = encoder.harmonize_eq_or_ite_terms(seq_term, vec_term);

    // Both should now be Seq-sorted
    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);
    assert_eq!(
        a_sort,
        Sort::seq(Sort::Int),
        "First operand should remain Seq(Int), got {a_sort:?}"
    );
    assert_eq!(
        b_sort,
        Sort::seq(Sort::Int),
        "Vec operand should be bridged to Seq(Int), got {b_sort:?}"
    );
}

/// Reverse order: Uninterpreted("Vec") vs Seq(Int) should also bridge. (#2699)
#[test]
#[timeout(30000)]
fn test_harmonize_uninterpreted_vec_vs_seq_bridges_to_seq() {
    let mut encoder = AYEncoder::new();
    let vec_sort = Sort::Uninterpreted("Vec".to_string());
    let vec_term = encoder.solver.declare_const("vec_val", vec_sort);
    let seq_term = encoder
        .solver
        .declare_const("seq_val", Sort::seq(Sort::Int));

    let (a, b) = encoder.harmonize_eq_or_ite_terms(vec_term, seq_term);

    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);
    assert_eq!(
        a_sort,
        Sort::seq(Sort::Int),
        "Vec operand should be bridged to Seq(Int), got {a_sort:?}"
    );
    assert_eq!(
        b_sort,
        Sort::seq(Sort::Int),
        "Second operand should remain Seq(Int), got {b_sort:?}"
    );
}

/// Datatype(Vec) vs Seq(Int) should bridge the Datatype to Seq. (#2699)
#[test]
#[timeout(30000)]
fn test_harmonize_datatype_vec_vs_seq_bridges_to_seq() {
    use ay_dpll::api::DatatypeSort;

    let mut encoder = AYEncoder::new();
    let dt_vec = Sort::Datatype(DatatypeSort {
        name: "Vec".to_string(),
        constructors: vec![],
    });
    let dt_term = encoder.solver.declare_const("dt_vec_val", dt_vec);
    let seq_term = encoder
        .solver
        .declare_const("seq_val", Sort::seq(Sort::Int));

    let (a, b) = encoder.harmonize_eq_or_ite_terms(dt_term, seq_term);

    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);
    assert_eq!(
        a_sort,
        Sort::seq(Sort::Int),
        "Datatype(Vec) should be bridged to Seq(Int), got {a_sort:?}"
    );
    assert_eq!(
        b_sort,
        Sort::seq(Sort::Int),
        "Second operand should remain Seq(Int), got {b_sort:?}"
    );
}

/// `safe_ite` with Seq and Vec branches should produce Seq-sorted result. (#2699)
#[test]
#[timeout(30000)]
fn test_safe_ite_seq_vs_vec_produces_seq_result() {
    let mut encoder = AYEncoder::new();
    let cond = encoder.solver.bool_const(true);
    let seq_term = encoder
        .solver
        .declare_const("seq_val", Sort::seq(Sort::Int));
    let vec_sort = Sort::Uninterpreted("Vec".to_string());
    let vec_term = encoder.solver.declare_const("vec_val", vec_sort);

    let result = encoder.safe_ite(cond, seq_term, vec_term);
    let result_sort = encoder.solver.get_sort(result);
    assert_eq!(
        result_sort,
        Sort::seq(Sort::Int),
        "safe_ite with Seq/Vec branches should produce Seq(Int), got {result_sort:?}"
    );
}

/// `is_seq_family_sort` should correctly classify sorts. (#2699)
#[test]
#[timeout(30000)]
fn test_is_seq_family_sort_classification() {
    use ay_dpll::api::DatatypeSort;

    use super::sort_context::is_seq_family_sort;

    // Seq family
    assert!(
        is_seq_family_sort(&Sort::seq(Sort::Int)),
        "Seq(Int) is Seq family"
    );
    assert!(
        is_seq_family_sort(&Sort::Uninterpreted("Vec".to_string())),
        "Vec is Seq family"
    );
    assert!(
        is_seq_family_sort(&Sort::Uninterpreted("VecDeque".to_string())),
        "VecDeque is Seq family"
    );
    assert!(
        is_seq_family_sort(&Sort::Uninterpreted("LinkedList".to_string())),
        "LinkedList is Seq family"
    );
    assert!(
        is_seq_family_sort(&Sort::Datatype(DatatypeSort {
            name: "Vec".to_string(),
            constructors: vec![],
        })),
        "Datatype(Vec) is Seq family"
    );

    // Not Seq family
    assert!(!is_seq_family_sort(&Sort::Int), "Int is not Seq family");
    assert!(!is_seq_family_sort(&Sort::Bool), "Bool is not Seq family");
    assert!(
        !is_seq_family_sort(&Sort::Uninterpreted("OptionInt".to_string())),
        "OptionInt is not Seq family"
    );
    assert!(
        !is_seq_family_sort(&Sort::Uninterpreted("FMap".to_string())),
        "FMap is not Seq family"
    );
    assert!(
        !is_seq_family_sort(&Sort::Uninterpreted("HashMap".to_string())),
        "HashMap is not Seq family"
    );
}

// === Seq element restoration in harmonize_eq_or_ite_terms (#2699) ===

/// When one side of equality is Int (from Seq element bridge) and the other
/// is a structural sort, `harmonize_eq_or_ite_terms` should try to restore
/// the bridged element to its original sort via `try_restore_seq_element_from_int`.
#[test]
#[timeout(30000)]
fn test_harmonize_restores_seq_element_to_mapping_sort() {
    use std::sync::Arc;

    use trust_wp_core::formula::{ExprSort, PureExpr};

    let mut encoder = AYEncoder::new();
    // Create a Seq variable and index into it to get an Int-bridged element
    let seq_var = PureExpr::Var("s".to_string(), Some(ExprSort::Seq));
    let index_expr = PureExpr::MethodCall {
        receiver: Arc::new(seq_var),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    let elem_term = encoder
        .encode_pure(&index_expr)
        .expect("seq index_logic should encode");
    assert_eq!(
        encoder.solver.get_sort(elem_term),
        Sort::Int,
        "Seq element should be Int-sorted from bridge"
    );

    // Create a Mapping-sorted term to compare against
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let mapping_term = encoder.solver.declare_const("m", mapping_sort.clone());

    // harmonize_eq_or_ite_terms should restore the Int element to Mapping
    let (a, b) = encoder.harmonize_eq_or_ite_terms(elem_term, mapping_term);
    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);
    // Both should be Mapping-sorted (or at least the same sort)
    assert_eq!(
        a_sort, b_sort,
        "After harmonization, both terms should have the same sort: a={a_sort:?}, b={b_sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn seq_element_closure_equality_restores_mapping_not_bool() {
    let mut encoder = AYEncoder::new();
    let seq_elem = PureExpr::MethodCall {
        receiver: Arc::new(var_with_sort("preds", ExprSort::Seq)),
        method: "index_logic".to_string(),
        args: vec![int(0)],
    };
    let closure = PureExpr::Closure {
        params: vec![("z".to_string(), Some(ExprSort::Int))],
        body: Arc::new(PureExpr::Bool(true)),
    };
    let equality = eq(seq_elem, closure);
    let seq_elem_for_check = if let PureExpr::BinOp(left, _, _) = &equality {
        left.as_ref().clone()
    } else {
        unreachable!()
    };
    let seq_receiver_is_seq = match &seq_elem_for_check {
        PureExpr::MethodCall { receiver, .. } => encoder.is_seq_receiver(receiver, None),
        _ => false,
    };

    let term = encoder
        .encode_pure(&equality)
        .expect("Seq<Mapping> element equality to closure should encode");

    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);
    let has_mapping_restore = encoder
        .seq_state_for_test()
        .get_seq_index_restore_fn("__seq_index_restore_Mapping")
        .is_some();
    let has_bool_restore = encoder
        .seq_state_for_test()
        .get_seq_index_restore_fn("__seq_index_restore_Bool")
        .is_some();
    let has_mapping_bridge = encoder.decls().has_spec_func("__to_mapping_Int");
    assert!(
        has_mapping_restore || has_mapping_bridge,
        "closure equality should coerce the Seq element as Mapping (bool_restore={has_bool_restore}, seq_receiver_is_seq={seq_receiver_is_seq})"
    );
    assert!(
        !has_bool_restore,
        "closure equality must not poison the Seq element as Bool"
    );
}

/// When both sides of an Ite are Datatype and Uninterpreted in the same
/// ADT family (e.g., OptionInt Datatype vs Option Uninterpreted),
/// `harmonize_eq_or_ite_terms` should resolve via structural sort target
/// instead of creating a fresh unconstrained constant. (#2699)
#[test]
#[timeout(30000)]
fn test_harmonize_cross_sort_type_option_family() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt_option = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "optionint_some_val".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.solver.declare_datatype(&dt_option);
    encoder.register_datatype("OptionInt".to_string(), dt_option.clone());

    let dt_sort = Sort::Datatype(dt_option);
    let ui_sort = Sort::Uninterpreted("OptionInt".to_string());
    let dt_term = encoder.solver.declare_const("dt_val", dt_sort.clone());
    let ui_term = encoder.solver.declare_const("ui_val", ui_sort);

    let (a, b) = encoder.harmonize_eq_or_ite_terms(dt_term, ui_term);
    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);

    // After harmonization, both should have the same sort (not a fresh constant)
    assert_eq!(
        a_sort, b_sort,
        "Cross-sort-type Option family should harmonize to same sort: a={a_sort:?}, b={b_sort:?}"
    );
}

/// Build the OptionInt datatype + register it on a fresh encoder, returning the
/// (datatype Sort, uninterpreted-ref Sort) pair used by the &mut Option
/// final-value bridge scenario (`lang/while_let.rs`).
#[cfg(test)]
fn option_family_sorts(encoder: &mut AYEncoder) -> (Sort, Sort) {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let dt_option = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "optionint_some_val".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.solver.declare_datatype(&dt_option);
    encoder.register_datatype("OptionInt".to_string(), dt_option.clone());
    // The reference carrier sort is the uninterpreted `Option` family member,
    // distinct as a Sort value but in the same structural family.
    (
        Sort::Datatype(dt_option),
        Sort::Uninterpreted("Option".to_string()),
    )
}

/// &mut Option final-value bridge: the loop_preservation obligation for
/// `lang/while_let.rs` (`*b = None` under `while let Some(_) = b`) has the
/// reference carrier `b_prime : Option` (uninterpreted) and the written deref
/// value `b_prime_current : OptionInt` (datatype) constrained to `None`. The
/// negated goal is `bridge(b_prime) != None`. Asserting the final-value bridge
/// equality (`b_prime == b_prime_current`, which `eq_term` routes through
/// `harmonize_eq_or_ite_terms` to the injective UF bridge
/// `bridge(b_prime) == b_prime_current`) makes the goal UNSAT — the case
/// verifies. This is the driver companion to the vacuous-trigger ay capability.
#[test]
#[timeout(30000)]
fn mut_option_final_value_bridge_refutes_preservation_goal() {
    let mut encoder = AYEncoder::new();
    let (dt_sort, ref_sort) = option_family_sorts(&mut encoder);

    // b_prime : Option (uninterpreted reference carrier)
    let b_prime = encoder.solver.declare_const("b_prime", ref_sort);
    // b_prime_current : OptionInt (datatype written value), constrained to None.
    let b_prime_current = encoder
        .solver
        .declare_const("b_prime_current", dt_sort.clone());
    let none_ctor = encoder
        .axiom_datatype_constructor("test/none", &dt_option_of(&dt_sort), "None", &[])
        .expect("None constructor for OptionInt");
    encoder.assert_eq(b_prime_current, none_ctor);

    // The final-value bridge equality (the fix): b_prime == b_prime_current,
    // routed through harmonize -> bridge(b_prime) == b_prime_current.
    encoder.assert_eq(b_prime, b_prime_current);

    // Negated preservation goal: bridge(b_prime) != None.
    let b_prime_sort = encoder.solver.get_sort(b_prime);
    let bridged = encoder.bridge_structural_sort(b_prime, &b_prime_sort, &dt_sort);
    let none_ctor2 = encoder
        .axiom_datatype_constructor("test/none2", &dt_option_of(&dt_sort), "None", &[])
        .expect("None constructor for OptionInt (goal)");
    let goal_neq = encoder.solver.neq(bridged, none_ctor2);
    encoder.solver.assert_term(goal_neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "with the &mut Option final-value bridge, bridge(b_prime) must equal None \
         (loop_preservation for lang/while_let goes sat->unsat)"
    );
}

/// SAT-preservation / soundness guard: the final-value bridge equality only
/// states that `bridge(b_prime)` equals the *written* value. It must NOT make
/// an unrelated false goal provable. Here b_prime_current is written `Some(5)`;
/// the bogus goal `bridge(b_prime) == None` does NOT follow and must stay SAT
/// (i.e., a preservation obligation that genuinely fails is NOT spuriously
/// accepted). This is the catastrophic-false-accept guard for the driver fix.
#[test]
#[timeout(30000)]
fn mut_option_final_value_bridge_does_not_prove_wrong_value() {
    let mut encoder = AYEncoder::new();
    let (dt_sort, ref_sort) = option_family_sorts(&mut encoder);

    let b_prime = encoder.solver.declare_const("b_prime", ref_sort);
    let b_prime_current = encoder
        .solver
        .declare_const("b_prime_current", dt_sort.clone());
    // Written value is Some(5), NOT None.
    let five = encoder.solver.int_const(5);
    let some_five = encoder
        .axiom_datatype_constructor("test/some", &dt_option_of(&dt_sort), "Some", &[five])
        .expect("Some constructor for OptionInt");
    encoder.assert_eq(b_prime_current, some_five);

    // Final-value bridge (the fix): b_prime == b_prime_current => bridge == Some(5).
    encoder.assert_eq(b_prime, b_prime_current);

    // Bogus goal: try to prove bridge(b_prime) == None. With Some(5) written,
    // this is FALSE, so asserting it must be SAT only if None == Some(5), which
    // the datatype disequality forbids => asserting (bridge == None) is UNSAT,
    // meaning the goal (bridge != None) is VALID, i.e. provable — correct, since
    // bridge IS Some(5) != None. The real soundness check: prove that we CANNOT
    // derive the *wrong* equation bridge == None.
    let b_prime_sort = encoder.solver.get_sort(b_prime);
    let bridged = encoder.bridge_structural_sort(b_prime, &b_prime_sort, &dt_sort);
    let none_ctor = encoder
        .axiom_datatype_constructor("test/none", &dt_option_of(&dt_sort), "None", &[])
        .expect("None constructor for OptionInt");
    let wrong_eq = encoder.solver.eq(bridged, none_ctor);
    encoder.solver.assert_term(wrong_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "bridge(b_prime) is Some(5); asserting bridge == None must be UNSAT — the \
         bridge never collapses distinct datatype values (no false-accept)"
    );
}

/// Helper: rebuild the OptionInt DatatypeSort from a Sort::Datatype for
/// constructor lookups inside the bridge tests.
#[cfg(test)]
fn dt_option_of(dt_sort: &Sort) -> ay_dpll::api::DatatypeSort {
    match dt_sort {
        Sort::Datatype(dt) => dt.clone(),
        _ => panic!("expected Sort::Datatype for OptionInt"),
    }
}

// =============================================================================
// Integer truncation via BV — cast semantics (#2666, #938)
//
// These tests validate `encode_int_truncation_bv`, which provides the ay-side
// infrastructure for replacing the IntegerCastIdentity unsoundness with exact
// BV truncation semantics. Rust's `value as u8` is modeled as
// `bv2int(bvextract(int2bv(value, 64), 7, 0))` — i.e., take the lower 8 bits.
// =============================================================================

/// Unsigned truncation: 300_u32 as u8 = 300 % 256 = 44.
///
/// This is the canonical unsound case for IntegerCastIdentity: trust-wp's
/// identity encoding keeps 300 as-is, but real Rust wraps to 44.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_unsigned_narrowing_u8() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(300);
    let truncated = encoder.encode_int_truncation_bv(value, 8, false);

    // Result should be Int-sorted (after bv2int).
    assert_eq!(encoder.solver.get_sort(truncated), Sort::Int);

    // 300 as u8 = 300 % 256 = 44
    let expected = encoder.solver.int_const(44);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "300 truncated to u8 should equal 44 (300 % 256)"
    );
}

/// Unsigned truncation: 0xFF_FF as u8 = 255.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_unsigned_narrowing_0xffff() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(0xFFFF);
    let truncated = encoder.encode_int_truncation_bv(value, 8, false);

    let expected = encoder.solver.int_const(255);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "0xFFFF truncated to u8 should equal 255"
    );
}

/// Unsigned truncation: value fits in target width (no change).
/// 100_u32 as u8 = 100 (fits in 8 bits).
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_unsigned_value_fits() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(100);
    let truncated = encoder.encode_int_truncation_bv(value, 8, false);

    let expected = encoder.solver.int_const(100);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "100 truncated to u8 should still be 100 (fits in 8 bits)"
    );
}

/// Unsigned truncation to u16: 70000 as u16 = 70000 % 65536 = 4464.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_unsigned_narrowing_u16() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(70000);
    let truncated = encoder.encode_int_truncation_bv(value, 16, false);

    let expected = encoder.solver.int_const(4464);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "70000 truncated to u16 should equal 4464 (70000 % 65536)"
    );
}

/// Signed truncation: 200_u32 as i8 = -56 (two's complement).
///
/// 200 in binary is 11001000. As a signed 8-bit integer (i8), the high
/// bit is 1, so the value is -(256 - 200) = -56.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_signed_narrowing_i8() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(200);
    let truncated = encoder.encode_int_truncation_bv(value, 8, true);

    assert_eq!(encoder.solver.get_sort(truncated), Sort::Int);

    // 200 as i8 = -56
    let expected = encoder.solver.int_const(-56);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "200 truncated to i8 (signed) should equal -56"
    );
}

/// Signed truncation: 127 as i8 = 127 (fits in signed range).
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_signed_value_fits() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(127);
    let truncated = encoder.encode_int_truncation_bv(value, 8, true);

    let expected = encoder.solver.int_const(127);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "127 truncated to i8 (signed) should still be 127"
    );
}

/// Signed truncation: 128 as i8 = -128 (overflow boundary).
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_signed_boundary_i8() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(128);
    let truncated = encoder.encode_int_truncation_bv(value, 8, true);

    // 128 as i8 = -128 (0x80 in two's complement)
    let expected = encoder.solver.int_const(-128);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "128 truncated to i8 (signed) should equal -128"
    );
}

/// Truncation to u32: 0xDEAD_BEEF_CAFE_i64 as u32 = 0xBEEF_CAFE.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_u32_from_large_value() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(0xDEAD_BEEF_CAFE_i64);
    let truncated = encoder.encode_int_truncation_bv(value, 32, false);

    let expected = encoder.solver.int_const(0xBEEF_CAFE_i64);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "0xDEAD_BEEF_CAFE truncated to u32 should equal 0xBEEF_CAFE"
    );
}

/// Zero truncation: 0 as u8 = 0 (should be trivially correct).
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_zero() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(0);
    let truncated = encoder.encode_int_truncation_bv(value, 8, false);

    let expected = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "0 truncated to u8 should equal 0"
    );
}

/// Sign-change cast: -1_i32 as u32. In Rust, this wraps to u32::MAX (4294967295).
/// In BV: -1 → int2bv(64) → extract 31..0 → bv2int(unsigned) = 2^32 - 1.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_sign_change_neg1_to_u32() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(-1);
    let truncated = encoder.encode_int_truncation_bv(value, 32, false);

    // -1_i32 as u32 = 4294967295 (u32::MAX)
    let expected = encoder.solver.int_const(4_294_967_295_i64);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "-1 truncated to u32 (unsigned) should equal 4294967295 (u32::MAX)"
    );
}

/// 64-bit truncation should be effectively a no-op for values that fit in u64.
/// The same-width extract case hits the `target_bits >= source_width` branch.
#[test]
#[timeout(30000)]
fn test_int_truncation_bv_same_width_64() {
    let mut encoder = AYEncoder::new();

    let value = encoder.solver.int_const(42);
    let truncated = encoder.encode_int_truncation_bv(value, 64, false);

    let expected = encoder.solver.int_const(42);
    let neq = encoder.solver.neq(truncated, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "42 truncated to u64 should equal 42 (same width, no truncation)"
    );
}

/// `select_structural_sort_target` should resolve Tuple2 Datatype vs Uninterpreted.
/// Both Datatype(Tuple2) and Uninterpreted("Tuple2") map to the same "Tuple2"
/// family, and Datatype should be preferred (higher strength). (#2699)
#[test]
#[timeout(30000)]
fn test_select_structural_sort_target_tuple2_datatype_vs_uninterpreted() {
    use ay_dpll::api::DatatypeSort;

    let dt_tuple = Sort::Datatype(DatatypeSort {
        name: "Tuple2".to_string(),
        constructors: vec![],
    });
    let uninterp_tuple = Sort::Uninterpreted("Tuple2".to_string());

    let result = super::select_structural_sort_target(&dt_tuple, &uninterp_tuple);
    assert_eq!(
        result,
        Some(dt_tuple.clone()),
        "Datatype(Tuple2) vs Uninterpreted(Tuple2) should prefer Datatype, got {result:?}"
    );

    // Also test reversed order
    let result_rev = super::select_structural_sort_target(&uninterp_tuple, &dt_tuple);
    assert_eq!(
        result_rev,
        Some(dt_tuple),
        "Uninterpreted(Tuple2) vs Datatype(Tuple2) should prefer Datatype, got {result_rev:?}"
    );
}

/// `safe_ite` should harmonize Tuple2 Datatype vs Uninterpreted without
/// panicking. This exercises the cross-sort-type Tuple family resolution
/// in the harmonization pipeline. (#2699)
#[test]
#[timeout(30000)]
fn test_safe_ite_harmonizes_tuple2_datatype_vs_uninterpreted() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let cond = encoder.solver.bool_const(true);

    let dt = DatatypeSort {
        name: "Tuple2".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk_Tuple2".to_string(),
            fields: vec![
                DatatypeField {
                    name: "_0".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "_1".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder.solver.declare_datatype(&dt);
    let then_term = encoder
        .solver
        .declare_const("t_dt", Sort::Datatype(dt.clone()));
    let else_term = encoder
        .solver
        .declare_const("t_ui", Sort::Uninterpreted("Tuple2".to_string()));

    // Should not panic — harmonization should handle the sort mismatch.
    let result = encoder.safe_ite(cond, then_term, else_term);
    let result_sort = encoder.solver.get_sort(result);

    // Result should not be Bool (that would indicate fallback failure).
    assert_ne!(
        result_sort,
        Sort::Bool,
        "safe_ite result for Tuple2 mismatch should not be Bool"
    );
}

/// `normalize_structural_sort_family` should map Seq-model type names to "Seq".
/// This ensures that Vec, VecDeque, LinkedList, and Seq all share the same
/// family for cross-sort coercion. (#2699)
#[test]
#[timeout(30000)]
fn test_normalize_structural_sort_family_seq_model_types() {
    use super::sort_context::sort_coercion::normalize_structural_sort_family;
    assert_eq!(normalize_structural_sort_family("Vec"), "Seq");
    assert_eq!(normalize_structural_sort_family("VecDeque"), "Seq");
    assert_eq!(normalize_structural_sort_family("LinkedList"), "Seq");
    assert_eq!(normalize_structural_sort_family("Seq"), "Seq");
}

/// `normalize_structural_sort_family` should map FMap-model type names to "FMap".
/// (#2699)
#[test]
#[timeout(30000)]
fn test_normalize_structural_sort_family_fmap_model_types() {
    use super::sort_context::sort_coercion::normalize_structural_sort_family;
    assert_eq!(normalize_structural_sort_family("HashMap"), "FMap");
    assert_eq!(normalize_structural_sort_family("GhostMap"), "FMap");
    assert_eq!(normalize_structural_sort_family("FMap"), "FMap");
}

/// `normalize_structural_sort_family` should map TupleN names to themselves.
/// Each Tuple arity has its own family. (#2699)
#[test]
#[timeout(30000)]
fn test_normalize_structural_sort_family_tuple_types() {
    use super::sort_context::sort_coercion::normalize_structural_sort_family;
    assert_eq!(normalize_structural_sort_family("Tuple2"), "Tuple2");
    assert_eq!(normalize_structural_sort_family("Tuple3"), "Tuple3");
    assert_eq!(normalize_structural_sort_family("Tuple10"), "Tuple10");
}

/// `select_structural_sort_target` should prefer a concrete sort over a
/// TypeParam Uninterpreted sort. TypeParam is a placeholder — the concrete
/// sort carries real type information. (#2699)
#[test]
#[timeout(30000)]
fn test_select_structural_sort_target_typaram_vs_concrete_datatype() {
    use ay_dpll::api::DatatypeSort;

    let typaram = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
    let dt = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![],
    });

    let result = super::select_structural_sort_target(&typaram, &dt);
    assert_eq!(
        result,
        Some(dt.clone()),
        "TypeParam vs Datatype should prefer Datatype, got {result:?}"
    );

    // Reversed order
    let result_rev = super::select_structural_sort_target(&dt, &typaram);
    assert_eq!(
        result_rev,
        Some(dt),
        "Datatype vs TypeParam should prefer Datatype, got {result_rev:?}"
    );
}

/// TypeParam vs Seq should prefer Seq. (#2699)
#[test]
#[timeout(30000)]
fn test_select_structural_sort_target_typaram_vs_seq() {
    let typaram = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
    let seq = Sort::seq(Sort::Int);

    let result = super::select_structural_sort_target(&typaram, &seq);
    assert_eq!(
        result,
        Some(seq.clone()),
        "TypeParam vs Seq should prefer Seq, got {result:?}"
    );

    let result_rev = super::select_structural_sort_target(&seq, &typaram);
    assert_eq!(
        result_rev,
        Some(seq),
        "Seq vs TypeParam should prefer Seq, got {result_rev:?}"
    );
}

/// TypeParam vs Int should prefer Int (Int is concrete, TypeParam is not). (#2699)
#[test]
#[timeout(30000)]
fn test_select_structural_sort_target_typaram_vs_int() {
    let typaram = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());

    let result = super::select_structural_sort_target(&typaram, &Sort::Int);
    assert_eq!(
        result,
        Some(Sort::Int),
        "TypeParam vs Int should prefer Int, got {result:?}"
    );

    let result_rev = super::select_structural_sort_target(&Sort::Int, &typaram);
    assert_eq!(
        result_rev,
        Some(Sort::Int),
        "Int vs TypeParam should prefer Int, got {result_rev:?}"
    );
}

/// `Bool vs Int` should prefer `Bool` so `eq_or_iff` uses `iff` instead of `eq`.
/// Int is the universal "unknown" sort from inference fallback; when the other side
/// is Bool, using `iff` is logically correct for Boolean equality. Without this,
/// the Eq/Ne path in operators.rs fires SortFallbackToInt. (#2663)
#[test]
#[timeout(30000)]
fn test_select_structural_sort_target_bool_vs_int() {
    let result = super::select_structural_sort_target(&Sort::Bool, &Sort::Int);
    assert_eq!(
        result,
        Some(Sort::Bool),
        "Bool vs Int should prefer Bool for correct iff dispatch, got {result:?}"
    );

    let result_rev = super::select_structural_sort_target(&Sort::Int, &Sort::Bool);
    assert_eq!(
        result_rev,
        Some(Sort::Bool),
        "Int vs Bool should prefer Bool for correct iff dispatch, got {result_rev:?}"
    );
}

/// End-to-end test: Eq comparison with Bool and Int operands should not fire
/// SortFallbackToInt after the Bool-vs-Int preference fix. (#2663)
#[test]
#[timeout(30000)]
fn test_eq_bool_vs_int_operands_no_sort_fallback() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new_all();
        let bool_var = encoder.solver.declare_const("b", Sort::Bool);
        let int_var = encoder.solver.declare_const("x", Sort::Int);

        // Encode Eq with one Bool and one Int operand — previously this
        // fired SortFallbackToInt because select_structural_sort_target
        // returned None for (None, None) when both are primitive sorts.
        let _eq_term = encoder
            .encode_binop(bool_var, BinOp::Eq, int_var, None)
            .expect("Eq encoding should succeed");

        let after = unsoundness::snapshot();
        let delta = unsoundness::delta(&before, &after);
        assert!(
            !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
            "Eq with Bool vs Int operands should NOT fire SortFallbackToInt \
             after Bool-vs-Int preference fix: {delta:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ── parse_int_truncate_name tests (#2666) ─────────────────────────────

#[test]
fn test_parse_int_truncate_name_unsigned_8() {
    use crate::encoder::pure_encoding::parse_int_truncate_name;
    let result = parse_int_truncate_name("__trust_wp_int_truncate_u8");
    assert_eq!(result, Some((8, false)));
}

#[test]
fn test_parse_int_truncate_name_signed_16() {
    use crate::encoder::pure_encoding::parse_int_truncate_name;
    let result = parse_int_truncate_name("__trust_wp_int_truncate_s16");
    assert_eq!(result, Some((16, true)));
}

#[test]
fn test_parse_int_truncate_name_unsigned_32() {
    use crate::encoder::pure_encoding::parse_int_truncate_name;
    let result = parse_int_truncate_name("__trust_wp_int_truncate_u32");
    assert_eq!(result, Some((32, false)));
}

#[test]
fn test_parse_int_truncate_name_signed_64() {
    use crate::encoder::pure_encoding::parse_int_truncate_name;
    let result = parse_int_truncate_name("__trust_wp_int_truncate_s64");
    assert_eq!(result, Some((64, true)));
}

#[test]
fn test_parse_unsigned_to_signed_same_width_cast_name() {
    use crate::encoder::pure_encoding::parse_unsigned_to_signed_same_width_cast_name;
    assert_eq!(
        parse_unsigned_to_signed_same_width_cast_name("__trust_wp_int_cast_u64_to_s64"),
        Some(64)
    );
    assert_eq!(
        parse_unsigned_to_signed_same_width_cast_name("__trust_wp_int_cast_u32_to_s64"),
        None
    );
    assert_eq!(
        parse_unsigned_to_signed_same_width_cast_name("__trust_wp_int_truncate_s64"),
        None
    );
}

#[test]
fn test_parse_int_truncate_name_not_truncate() {
    use crate::encoder::pure_encoding::parse_int_truncate_name;
    assert_eq!(parse_int_truncate_name("size_of_logic"), None);
    assert_eq!(parse_int_truncate_name("__trust_wp_bit_and"), None);
    assert_eq!(parse_int_truncate_name("__trust_wp_int_truncate_"), None);
    assert_eq!(parse_int_truncate_name("__trust_wp_int_truncate_x8"), None);
}

/// End-to-end: `__trust_wp_int_truncate_u8(300)` should encode as 300 % 256 = 44.
///
/// Exercises the LogicFnCall → `encode_int_truncation_bv` interception path
/// that the driver uses for narrowing IntToInt casts (#2666, #938).
#[test]
#[timeout(30000)]
fn test_int_truncate_via_logic_fn_call_u8() {
    let mut encoder = AYEncoder::new();

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_int_truncate_u8".to_string(),
        args: vec![PureExpr::Int(300)],
    };
    let result = encoder.encode_pure(&expr).expect("encoding should succeed");

    // 300 % 256 = 44
    let expected = encoder.solver.int_const(44);
    let neq = encoder.solver.neq(result, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "__trust_wp_int_truncate_u8(300) should equal 44 (modular truncation)"
    );
}

/// End-to-end: `__trust_wp_int_truncate_s8(200)` should encode as -56.
///
/// 200 in 8-bit unsigned is 0xC8. Interpreted as signed i8: -56.
#[test]
#[timeout(30000)]
fn test_int_truncate_via_logic_fn_call_s8() {
    let mut encoder = AYEncoder::new();

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_int_truncate_s8".to_string(),
        args: vec![PureExpr::Int(200)],
    };
    let result = encoder.encode_pure(&expr).expect("encoding should succeed");

    // 200 in i8: 200 - 256 = -56
    let expected = encoder.solver.int_const(-56);
    let neq = encoder.solver.neq(result, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "__trust_wp_int_truncate_s8(200) should equal -56 (signed modular truncation)"
    );
}

/// End-to-end: `__trust_wp_int_truncate_u32(-1)` should encode as 2^32 - 1 = 4294967295.
///
/// This exercises the sign-change cast path: `(-1_i32) as u32`.
#[test]
#[timeout(30000)]
fn test_int_truncate_via_logic_fn_call_sign_change() {
    let mut encoder = AYEncoder::new();

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_int_truncate_u32".to_string(),
        args: vec![PureExpr::Int(-1)],
    };
    let result = encoder.encode_pure(&expr).expect("encoding should succeed");

    // (-1) in u32: 2^32 - 1 = 4294967295
    let expected = encoder.solver.int_const(4_294_967_295_i64);
    let neq = encoder.solver.neq(result, expected);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "__trust_wp_int_truncate_u32(-1) should equal 4294967295 (unsigned wrap)"
    );
}

/// End-to-end: `__trust_wp_int_cast_u64_to_s64` uses arithmetic reinterpretation.
///
/// This avoids BV terms in same-width `usize as isize` casts while preserving
/// the unsigned source semantics at both sides of the signed boundary.
#[test]
#[timeout(30000)]
fn test_unsigned_to_signed_same_width_cast_via_logic_fn_call() {
    use num_bigint::BigInt;

    let mut low_encoder = AYEncoder::new();
    let low_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_int_cast_u64_to_s64".to_string(),
        args: vec![PureExpr::Int(42)],
    };
    let low = low_encoder
        .encode_pure(&low_expr)
        .expect("low cast encoding should succeed");
    let low_expected = low_encoder.solver.int_const(42);
    let low_neq = low_encoder.solver.neq(low, low_expected);
    low_encoder.solver.assert_term(low_neq);
    assert!(
        matches!(low_encoder.check_sat(), SolveResult::Unsat(_)),
        "u64 value in signed positive range should remain unchanged"
    );

    let mut high_encoder = AYEncoder::new();
    let high_arg = high_encoder
        .solver
        .int_const_bigint(&(BigInt::from(1u8) << 63));
    let high = high_encoder.encode_unsigned_to_signed_same_width(high_arg, 64);
    let high_expected = high_encoder.solver.int_const(i64::MIN);
    let high_neq = high_encoder.solver.neq(high, high_expected);
    high_encoder.solver.assert_term(high_neq);
    assert!(
        matches!(high_encoder.check_sat(), SolveResult::Unsat(_)),
        "2^63 as i64 should become i64::MIN"
    );
}

#[test]
#[timeout(30000)]
fn test_unsigned_to_signed_same_width_cast_symbolic_small_bound_identity() {
    let mut encoder = AYEncoder::new();

    let x = encoder.solver.declare_const("knights_cast_x", Sort::Int);
    let size = encoder.solver.declare_const("knights_cast_size", Sort::Int);
    let casted = encoder.encode_unsigned_to_signed_same_width(x, 64);

    let zero = encoder.solver.int_const(0);
    let board_limit = encoder.solver.int_const(1000);
    let x_nonnegative = encoder.solver.ge(x, zero);
    let x_below_size = encoder.solver.lt(x, size);
    let size_within_limit = encoder.solver.le(size, board_limit);
    encoder.solver.assert_term(x_nonnegative);
    encoder.solver.assert_term(x_below_size);
    encoder.solver.assert_term(size_within_limit);

    let cast_matches_source = encoder.solver.eq(casted, x);
    let cast_below_size = encoder.solver.lt(casted, size);
    let goal = encoder.solver.and(cast_matches_source, cast_below_size);
    let negated_goal = encoder.solver.not(goal);
    encoder.solver.assert_term(negated_goal);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "small nonnegative usize-as-isize casts should stay unchanged and below size; got {result:?}"
    );
}

// === Same-family structural bridging in harmonize_eq_or_ite_terms (#2699) ===

/// When one ITE operand is `Datatype(Adt_Some_None)` and the other is
/// `Uninterpreted("OptionInt")`, `harmonize_eq_or_ite_terms` should use an
/// injective UF bridge instead of a fresh unconstrained constant. Both
/// operands should end up with the same sort. (#2699)
#[test]
#[timeout(30000)]
fn test_harmonize_option_dt_vs_uninterpreted_bridges_to_same_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let option_dt_sort = Sort::Datatype(DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });
    let option_ui_sort = Sort::Uninterpreted("OptionInt".to_string());

    let dt_term = encoder
        .solver
        .declare_const("option_dt_val", option_dt_sort.clone());
    let ui_term = encoder
        .solver
        .declare_const("option_ui_val", option_ui_sort);

    let (a, b) = encoder.harmonize_eq_or_ite_terms(dt_term, ui_term);

    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);
    assert_eq!(
        a_sort, b_sort,
        "same-family bridging should produce matching sorts: a={a_sort:?} b={b_sort:?}"
    );
}

/// Reverse order: `Uninterpreted("OptionInt")` vs `Datatype(Adt_Some_None)`. (#2699)
#[test]
#[timeout(30000)]
fn test_harmonize_uninterpreted_vs_option_dt_bridges_to_same_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let option_dt_sort = Sort::Datatype(DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });
    let option_ui_sort = Sort::Uninterpreted("OptionInt".to_string());

    let ui_term = encoder
        .solver
        .declare_const("option_ui_val", option_ui_sort);
    let dt_term = encoder
        .solver
        .declare_const("option_dt_val", option_dt_sort);

    let (a, b) = encoder.harmonize_eq_or_ite_terms(ui_term, dt_term);

    let a_sort = encoder.solver.get_sort(a);
    let b_sort = encoder.solver.get_sort(b);
    assert_eq!(
        a_sort, b_sort,
        "reverse same-family bridging should produce matching sorts: a={a_sort:?} b={b_sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_option_payload_none_equality_uses_peer_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&own_result);
    let option_own_result =
        encoder.stdlib_option_datatype_for_payload_sort(Sort::Datatype(own_result));
    encoder.ensure_datatype_declared(&option_own_result);
    let _ = encoder
        .get_or_declare_var("result", Sort::Datatype(option_own_result.clone()))
        .expect("result should predeclare with Option payload datatype");

    let none = PureExpr::LogicFnCall {
        name: "None".to_string(),
        args: vec![],
    };
    let result_not_none = ne(var("result"), none);
    let term = encoder
        .encode_pure(&result_not_none)
        .expect("result != None should use result's Option payload datatype");

    assert_eq!(encoder.solver.get_sort(term), Sort::Bool);
    assert!(
        matches!(encoder.var_sort("result"), Some(Sort::Datatype(dt)) if dt.name == option_own_result.name),
        "contextual None encoding must not downgrade result to OptionInt"
    );
}

#[test]
#[timeout(30000)]
fn test_option_payload_some_is_distinct_from_contextual_none() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&own_result);

    let some_err = PureExpr::LogicFnCall {
        name: "Some".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "OwnResult::Err".to_string(),
            args: vec![int(7)],
        }],
    };
    let none = PureExpr::LogicFnCall {
        name: "None".to_string(),
        args: vec![],
    };
    let some_not_none = ne(some_err, none);
    let term = encoder
        .encode_pure(&some_not_none)
        .expect("Some(OwnResult::Err(_)) != None should encode in one Option datatype");
    let negated = encoder.solver.not(term);
    encoder.solver.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Some(payload) must be distinct from contextual None, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_structural_bridge_same_term_sort_is_identity() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let option_dt_sort = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });
    let option_ui_sort = Sort::Uninterpreted("OptionInt".to_string());
    let dt_term = encoder
        .solver
        .declare_const("option_same_term_sort_val", option_dt_sort.clone());

    let bridged = encoder.bridge_structural_sort(dt_term, &option_dt_sort, &option_ui_sort);

    assert_eq!(
        bridged, dt_term,
        "same term-store sort structural bridge should be identity"
    );
    assert!(
        !encoder.has_logic_func_decl("__trust_wp_struct_bridge_OptionInt_to_OptionInt"),
        "identity bridge must not declare a UF or assert an injectivity quantifier"
    );
}

#[test]
#[timeout(30000)]
fn test_eq_term_uninterpreted_list_vs_synthesized_adt_cons_nil_does_not_panic() {
    let mut encoder = AYEncoder::new();
    let list = encoder
        .solver
        .declare_const("list_value", Sort::Uninterpreted("List".to_string()));
    let synthesized = encoder.solver.declare_const(
        "adt_cons_nil_value",
        Sort::Uninterpreted("Adt_Cons_Nil".to_string()),
    );

    let eq = encoder.eq_term(list, synthesized);
    assert_eq!(encoder.solver.get_sort(eq), Sort::Bool);
    encoder.assert_term(eq);

    let _ = encoder.check_sat();
    assert!(
        encoder.solver_panic_reason().is_none(),
        "eq_term should harmonize List and Adt_Cons_Nil without recording a solver panic: {:?}",
        encoder.solver_panic_reason()
    );
}

/// `same_structural_family` should detect cross-sort-type families. (#2699)
#[test]
#[timeout(30000)]
fn test_same_structural_family_option_family() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let dt = Sort::Datatype(DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });
    let ui = Sort::Uninterpreted("OptionInt".to_string());
    let family = super::sort_context::same_structural_family(&dt, &ui);
    assert_eq!(
        family,
        Some("Option".to_string()),
        "Adt_Some_None and OptionInt should be in Option family"
    );
}

/// `same_structural_family` should return None for unrelated families. (#2699)
#[test]
#[timeout(30000)]
fn test_same_structural_family_different_families() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let option_dt = Sort::Datatype(DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });
    let result_ui = Sort::Uninterpreted("ResultIntInt".to_string());
    let family = super::sort_context::same_structural_family(&option_dt, &result_ui);
    assert_eq!(
        family, None,
        "Option and Result should not be in the same family"
    );
}

// ── Signed narrow-width bitwise hint (#route-100 rightmostbit) ──────────
//
// `encode_int_binop_bv` historically encoded EVERY Int-sorted bitwise op at
// width 64 with an UNSIGNED bv2int wrap-back — a latent FALSE-REJECT for
// signed narrow types (i8 `x & y` with negative operands decodes to
// `2^64 - k` instead of the negative result). With premise-registered
// signed-window hints, `&`/`|`/`^` encode exactly at the source width with
// a SIGNED wrap-back.

/// Requires shaped exactly like the driver's injected i8 range facts.
fn i8_window_requires(names: &[&str]) -> Vec<PureExpr> {
    let mut requires = Vec::new();
    for name in names {
        let v = || PureExpr::View(Arc::new(var(name)));
        requires.push(binop(v(), BinOp::Ge, int(-128)));
        requires.push(binop(v(), BinOp::Le, int(127)));
    }
    requires
}

#[test]
#[timeout(30000)]
fn test_signed_window_hint_registration_and_derivation() {
    let mut encoder = AYEncoder::new();
    encoder.register_signed_window_hints(&i8_window_requires(&["x", "y"]));

    // Both hinted at the same width -> Some(8).
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("x"), &var("y")),
        Some(8)
    );
    // Hinted var + literal inside the window -> Some(8); outside -> None.
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("x"), &int(1)),
        Some(8)
    );
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("x"), &int(-128)),
        Some(8)
    );
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("x"), &int(200)),
        None
    );
    // Unhinted operand -> None (fail closed).
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("x"), &var("z")),
        None
    );
    // View/old wrappers name the same integer value.
    let x_view = PureExpr::View(Arc::new(var("x")));
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&x_view, &var("y")),
        Some(8)
    );
}

#[test]
#[timeout(30000)]
fn test_signed_window_hint_rejects_non_window_and_unsigned_pairs() {
    let mut encoder = AYEncoder::new();
    // Unsigned window (0..=255): NOT a signed window — no hint.
    let v = || PureExpr::View(Arc::new(var("u")));
    let unsigned = vec![
        binop(v(), BinOp::Ge, int(0)),
        binop(v(), BinOp::Le, int(255)),
    ];
    encoder.register_signed_window_hints(&unsigned);
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("u"), &var("u")),
        None
    );
    // Asymmetric bounds (user precondition, not a type window) — no hint.
    let w = || PureExpr::View(Arc::new(var("w")));
    let asymmetric = vec![
        binop(w(), BinOp::Ge, int(-100)),
        binop(w(), BinOp::Le, int(100)),
    ];
    encoder.register_signed_window_hints(&asymmetric);
    assert_eq!(
        encoder.signed_narrow_bitwise_hint(&var("w"), &var("w")),
        None
    );
}

/// With the signed i8 hint, the bridge encodes at WIDTH 8 with the SIGNED
/// wrap-back (`bv2nat(r) - 256` when the sign bit is set) — the exact i8
/// semantics — instead of the historical width-64 unsigned `bv2nat` that
/// mis-decoded negative results (e.g. `-3 & -5` as `2^64 - 7`).
#[test]
#[timeout(30000)]
fn test_signed_hinted_bitand_encodes_width8_signed_wrapback() {
    let mut encoder = AYEncoder::new();
    encoder.register_signed_window_hints(&i8_window_requires(&["x", "y"]));

    let x = encoder.solver.declare_const("x", Sort::Int);
    let y = encoder.solver.declare_const("y", Sort::Int);
    let result = encoder
        .encode_binop_with_bv_hint(x, BinOp::BitAnd, y, None, Some(8))
        .expect("hinted bitand encodes");

    let formatted = encoder.solver.format_term(result);
    assert!(
        formatted.contains("(_ int2bv 8)"),
        "hinted encoding must use the source width 8, got: {formatted}"
    );
    assert!(
        !formatted.contains("(_ int2bv 64)"),
        "hinted encoding must not fall back to width 64, got: {formatted}"
    );
    // Signed wrap-back: negative sign bit subtracts the modulus.
    assert!(
        formatted.contains("bvslt") && formatted.contains("256"),
        "hinted encoding must apply the signed (two's-complement) \
         conversion, got: {formatted}"
    );
}

/// The unhinted path is byte-for-byte unchanged: width-64 unsigned bridge
/// (no regression from the hint plumbing).
#[test]
#[timeout(30000)]
fn test_unhinted_bitand_encoding_unchanged() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver.declare_const("x", Sort::Int);
    let y = encoder.solver.declare_const("y", Sort::Int);
    let result = encoder
        .encode_binop(x, BinOp::BitAnd, y, None)
        .expect("bitand encodes");
    assert_eq!(
        encoder.solver.format_term(result),
        "(bv2nat (bvand ((_ int2bv 64) x) ((_ int2bv 64) y)))",
        "unhinted bitwise encoding must stay the historical width-64 \
         unsigned bridge"
    );
}
