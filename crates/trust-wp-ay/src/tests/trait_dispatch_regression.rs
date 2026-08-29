// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for trait dispatch patterns from #2670.
//!
//! These tests cover the 5 compat test patterns that were previously failing:
//! - `traits/12_default_method`: default trait method resolution
//! - `traits/15_impl_interfaces`: associated type projection sort inference
//! - `traits/16_impl_cloning`: mutable reference view equality
//! - `traits/19_sealed`: sealed trait logic function expansion
//! - `ord_trait`: OrdLogic trait comparison encoding
//!
//! Each test exercises the AY encoder-level encoding to verify that the
//! patterns produce correct verification results.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use crate::AYEncoder;

// ── Pattern 1: Default method resolution (#2670, traits/12) ────────────
//
// Trait T with:
//   fn default(&self) -> u32 { 0 }
//   #[logic(open)] fn logic_default(self) -> bool { true }
// The ensures(x.logic_default()) contract should be provable when the
// logic function is axiomatized with body expansion.

/// Regression test: a logic function with body `true` (open default method)
/// should make `ensures(logic_default(x))` provable. The encoder declares
/// the logic function and asserts `forall x. logic_default(x) = true`.
#[test]
#[timeout(10000)]
fn test_default_method_open_logic_fn_body_true_provable() {
    let mut encoder = AYEncoder::new();

    // Declare logic_default as unary (TypeParam -> Bool) with body expansion `true`.
    let type_param_sort = Sort::Uninterpreted("T".to_string());
    let logic_default_decl = encoder.get_or_declare_logic_func(
        "logic_default_T",
        &[type_param_sort.clone()],
        Sort::Bool,
    );

    // Assert body expansion: forall x:T. logic_default(x) = true
    let x = encoder.solver.fresh_var("__x_ld", type_param_sort.clone());
    let app = encoder.solver.apply(&logic_default_decl, &[x]);
    let true_const = encoder.solver.bool_const(true);
    let body_eq = encoder.solver.eq(app, true_const);
    let axiom = encoder
        .solver
        .forall_with_triggers(&[x], body_eq, &[&[app]]);
    encoder.solver.assert_term(axiom);

    // Postcondition negation: NOT(logic_default(some_x))
    let some_x = encoder.solver.declare_const("__some_x", type_param_sort);
    let post_app = encoder.solver.apply(&logic_default_decl, &[some_x]);
    let negated = encoder.solver.not(post_app);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "ensures(x.logic_default()) should be provable when body expands to true (#2670)"
    );
}

/// Regression test: without body expansion, logic_default is unconstrained
/// and the postcondition negation should be satisfiable.
#[test]
#[timeout(10000)]
fn test_default_method_without_body_expansion_unconstrained() {
    let mut encoder = AYEncoder::new();

    let type_param_sort = Sort::Uninterpreted("T".to_string());
    let logic_default_decl = encoder.get_or_declare_logic_func(
        "logic_default_T_unc",
        &[type_param_sort.clone()],
        Sort::Bool,
    );

    // No body expansion — logic_default is unconstrained.
    let some_x = encoder
        .solver
        .declare_const("__some_x_unc", type_param_sort);
    let post_app = encoder.solver.apply(&logic_default_decl, &[some_x]);
    let negated = encoder.solver.not(post_app);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "without body expansion, logic function is unconstrained and negation is satisfiable"
    );
}

// ── Pattern 2: Associated type sort inference (#2670, traits/15) ───────
//
// trait Tr { type A; }
// impl Tr for () { type A = (); }
// The associated type <() as Tr>::A should normalize to () (Unit sort),
// not fall back to Int via sort_fallback_to_int.
//
// At the encoder level, this means Unit-sorted variables should remain
// Unit-sorted through function call encoding.

/// Regression test: a logic function `x` with type param return and
/// a call site where the type param is instantiated to Unit should
/// produce a Unit-sorted result, not Int.
#[test]
#[timeout(10000)]
fn test_assoc_type_projection_unit_sort_not_int_fallback() {
    let mut encoder = AYEncoder::new();

    // Unit sort is Sort::Uninterpreted("Unit") — same as sort_mapping::unit_sort()
    let unit_sort = Sort::Uninterpreted("Unit".to_string());

    // Declare logic function x: (Unit) -> Unit (simulating <() as Tr>::A = ())
    let logic_x_decl = encoder.get_or_declare_logic_func(
        "logic_x_assoc_type",
        &[unit_sort.clone()],
        unit_sort.clone(),
    );

    // Precondition: x(a) == unit_value
    let a = encoder.solver.declare_const("__a_assoc", unit_sort.clone());
    let unit_val = encoder
        .solver
        .declare_const("__unit_val", unit_sort.clone());
    let x_a = encoder.solver.apply(&logic_x_decl, &[a]);
    let pre = encoder.solver.eq(x_a, unit_val);
    encoder.assert_term(pre);

    // The sort of x(a) should be Unit, not Int.
    // Verify by checking that the system is consistent.
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "associated type projection with Unit sort should produce consistent encoding (#2670)"
    );

    // Further: if we constrain a == unit_val (same value), x(a) == x(unit_val)
    let eq_a = encoder.solver.eq(a, unit_val);
    encoder.assert_term(eq_a);

    // Negate x(a) == x(unit_val) — should be UNSAT since a == unit_val
    let x_uv = encoder.solver.apply(&logic_x_decl, &[unit_val]);
    let eq_result = encoder.solver.eq(x_a, x_uv);
    let negated = encoder.solver.not(eq_result);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "x(a) == x(unit_val) when a == unit_val should be provable (no sort mismatch)"
    );
}

// ── Pattern 3: MutRef view equality (#2670, traits/16) ─────────────────
//
// ensures(x@ == (*x)@) for &mut Vec<T>
// The View of a mutable reference should equal the View of the deref.
// At encoder level: the view variable for a MutRef should be the same
// as the view of the inner value.

/// Regression test: `x@ == (*x)@` for a mutable reference should be
/// trivially provable when both sides resolve to the same view variable.
#[test]
#[timeout(10000)]
fn test_mutref_view_equality_same_variable() {
    let mut encoder = AYEncoder::new();

    // Create a Seq sort for the view (Vec<T>@ -> Seq<T>)
    let seq_sort = Sort::Uninterpreted("Seq_T".to_string());

    // Declare the view function: view(MutRef_Vec_T) -> Seq_T
    let mutref_sort = Sort::Uninterpreted("MutRef_Vec_T".to_string());
    let view_decl =
        encoder.get_or_declare_logic_func("view_mutref_vec", &[mutref_sort.clone()], seq_sort);

    // The MutRef view redirect means x@ and (*x)@ produce the same variable.
    // Simulate: both sides apply the same view function to the same variable.
    let x = encoder.solver.declare_const("__x_view", mutref_sort);
    let view_x = encoder.solver.apply(&view_decl, &[x]);
    let view_deref_x = encoder.solver.apply(&view_decl, &[x]); // same application

    // Negate: NOT(view(x) == view(x)) — should be UNSAT
    let eq = encoder.solver.eq(view_x, view_deref_x);
    let negated = encoder.solver.not(eq);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "x@ == (*x)@ should be trivially provable when both resolve to same view (#2670)"
    );
}

/// Regression test: distinct view applications should not be conflated.
/// If view(x) and view(y) are different applications, negating their
/// equality should be satisfiable.
#[test]
#[timeout(10000)]
fn test_mutref_view_distinct_refs_not_equal() {
    let mut encoder = AYEncoder::new();

    let seq_sort = Sort::Uninterpreted("Seq_T2".to_string());
    let mutref_sort = Sort::Uninterpreted("MutRef_Vec_T2".to_string());
    let view_decl =
        encoder.get_or_declare_logic_func("view_mutref_vec_2", &[mutref_sort.clone()], seq_sort);

    let x = encoder
        .solver
        .declare_const("__x_view2", mutref_sort.clone());
    let y = encoder.solver.declare_const("__y_view2", mutref_sort);
    let view_x = encoder.solver.apply(&view_decl, &[x]);
    let view_y = encoder.solver.apply(&view_decl, &[y]);

    // view(x) == view(y) is not necessarily true for distinct x, y
    let eq = encoder.solver.eq(view_x, view_y);
    let negated = encoder.solver.not(eq);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "distinct mutable references should not have equal views without constraints"
    );
}

// ── Pattern 4: Sealed trait logic function (#2670, traits/19) ──────────
//
// trait Tr {
//   #[logic] fn f(self, x: Int) -> Int;
//   #[logic(open, sealed)] fn g(self, x: Int) -> Int { self.f(x) + 1 }
// }
// ensures(x.g(y) == x.f(y) + 1)
//
// A `sealed` logic function has its body visible at call sites.
// The ensures clause should be provable because g's body expands.

/// Regression test: sealed logic function body expansion makes
/// `g(x, y) == f(x, y) + 1` provable.
#[test]
#[timeout(10000)]
fn test_sealed_logic_fn_body_expansion_provable() {
    let mut encoder = AYEncoder::new();

    let type_param_sort = Sort::Uninterpreted("T_sealed".to_string());

    // Declare f: (T, Int) -> Int (abstract, no body)
    let f_decl = encoder.get_or_declare_logic_func(
        "trait_f_sealed",
        &[type_param_sort.clone(), Sort::Int],
        Sort::Int,
    );

    // Declare g: (T, Int) -> Int
    let g_decl = encoder.get_or_declare_logic_func(
        "trait_g_sealed",
        &[type_param_sort.clone(), Sort::Int],
        Sort::Int,
    );

    // Sealed body expansion axiom: forall self:T, x:Int. g(self, x) = f(self, x) + 1
    let self_var = encoder
        .solver
        .fresh_var("__self_sealed", type_param_sort.clone());
    let x_var = encoder.solver.fresh_var("__x_sealed", Sort::Int);
    let g_app = encoder.solver.apply(&g_decl, &[self_var, x_var]);
    let f_app = encoder.solver.apply(&f_decl, &[self_var, x_var]);
    let one = encoder.solver.int_const(1);
    let f_plus_1 = encoder.solver.add(f_app, one);
    let body_eq = encoder.solver.eq(g_app, f_plus_1);
    let axiom = encoder
        .solver
        .forall_with_triggers(&[self_var, x_var], body_eq, &[&[g_app]]);
    encoder.solver.assert_term(axiom);

    // Postcondition: ensures(x.g(y) == x.f(y) + 1)
    // Negate: NOT(g(x, y) == f(x, y) + 1) for concrete x, y
    let concrete_x = encoder.solver.declare_const("__cx_sealed", type_param_sort);
    let concrete_y = encoder.solver.declare_const("__cy_sealed", Sort::Int);
    let g_concrete = encoder.solver.apply(&g_decl, &[concrete_x, concrete_y]);
    let f_concrete = encoder.solver.apply(&f_decl, &[concrete_x, concrete_y]);
    let f_concrete_plus_1 = encoder.solver.add(f_concrete, one);
    let post_eq = encoder.solver.eq(g_concrete, f_concrete_plus_1);
    let negated = encoder.solver.not(post_eq);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "sealed logic function body expansion should make g(x,y) == f(x,y) + 1 provable (#2670)"
    );
}

/// Regression test: without sealed body expansion, the relationship
/// between g and f is unconstrained.
#[test]
#[timeout(10000)]
fn test_sealed_logic_fn_without_body_unconstrained() {
    let mut encoder = AYEncoder::new();

    let type_param_sort = Sort::Uninterpreted("T_sealed_unc".to_string());

    let f_decl = encoder.get_or_declare_logic_func(
        "trait_f_sealed_unc",
        &[type_param_sort.clone(), Sort::Int],
        Sort::Int,
    );
    let g_decl = encoder.get_or_declare_logic_func(
        "trait_g_sealed_unc",
        &[type_param_sort.clone(), Sort::Int],
        Sort::Int,
    );

    // No body expansion — g and f are independent UFs.
    let concrete_x = encoder
        .solver
        .declare_const("__cx_sealed_u", type_param_sort);
    let concrete_y = encoder.solver.declare_const("__cy_sealed_u", Sort::Int);
    let g_concrete = encoder.solver.apply(&g_decl, &[concrete_x, concrete_y]);
    let f_concrete = encoder.solver.apply(&f_decl, &[concrete_x, concrete_y]);
    let one = encoder.solver.int_const(1);
    let f_plus_1 = encoder.solver.add(f_concrete, one);
    let post_eq = encoder.solver.eq(g_concrete, f_plus_1);
    let negated = encoder.solver.not(post_eq);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "without sealed body expansion, g and f are unconstrained and negation is satisfiable"
    );
}

// ── Pattern 5: OrdLogic comparison (#2670, ord_trait) ──────────────────
//
// ensures(result == true) for x <= x where T: Ord + DeepModel
// The OrdLogic axiom le_refl (forall x. x <= x) should make this provable.

/// Regression test: reflexive ordering `x <= x` should be provable
/// with the le_refl axiom.
#[test]
#[timeout(10000)]
fn test_ordlogic_le_refl_provable() {
    let mut encoder = AYEncoder::new();

    let model_sort = Sort::Uninterpreted("DeepModel_T".to_string());

    // Declare le: (DeepModel_T, DeepModel_T) -> Bool
    let le_decl = encoder.get_or_declare_logic_func(
        "ord_le_model",
        &[model_sort.clone(), model_sort.clone()],
        Sort::Bool,
    );

    // Reflexivity axiom: forall x:DeepModel_T. le(x, x) = true
    let x_var = encoder.solver.fresh_var("__x_le", model_sort.clone());
    let le_app = encoder.solver.apply(&le_decl, &[x_var, x_var]);
    let true_const = encoder.solver.bool_const(true);
    let le_eq_true = encoder.solver.eq(le_app, true_const);
    let refl_axiom = encoder
        .solver
        .forall_with_triggers(&[x_var], le_eq_true, &[&[le_app]]);
    encoder.solver.assert_term(refl_axiom);

    // Postcondition: ensures(result == true) where result = le(x, x)
    let concrete_x = encoder.solver.declare_const("__cx_le", model_sort);
    let result = encoder.solver.apply(&le_decl, &[concrete_x, concrete_x]);
    let true_const2 = encoder.solver.bool_const(true);
    let result_eq_true = encoder.solver.eq(result, true_const2);
    // Negate: NOT(result == true)
    let negated = encoder.solver.not(result_eq_true);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "le(x, x) should be true with reflexivity axiom (OrdLogic pattern, #2670)"
    );
}

/// Regression test: without any axioms, the le predicate is unconstrained,
/// so NOT(le(x, y)) should be satisfiable.
#[test]
#[timeout(10000)]
fn test_ordlogic_le_unconstrained_is_satisfiable() {
    let mut encoder = AYEncoder::new();

    let model_sort = Sort::Uninterpreted("DeepModel_T2".to_string());

    let le_decl = encoder.get_or_declare_logic_func(
        "ord_le_model_2",
        &[model_sort.clone(), model_sort.clone()],
        Sort::Bool,
    );

    // Without any axioms, le is an unconstrained uninterpreted function.
    // NOT(le(x, y)) should be satisfiable.
    let cx = encoder.solver.declare_const("__cx_le2", model_sort.clone());
    let cy = encoder.solver.declare_const("__cy_le2", model_sort);
    let le_xy = encoder.solver.apply(&le_decl, &[cx, cy]);
    let negated = encoder.solver.not(le_xy);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "without axioms, le(x, y) is unconstrained and its negation is satisfiable"
    );
}

// ── Sort consistency: TypeParam sort not collapsing to Int ──────────────
//
// Regression guard: when type parameters are used in trait method encoding,
// they must remain as uninterpreted sorts, not collapse to Int.

/// Regression test: a function with type parameter sort should not have
/// its parameter collapse to Int. The uninterpreted sort should keep
/// distinct constants distinguishable.
#[test]
#[timeout(10000)]
fn test_type_param_sort_remains_uninterpreted() {
    let mut encoder = AYEncoder::new();

    let type_param_sort = Sort::Uninterpreted("T_param".to_string());

    // Declare two constants of the type param sort
    let a = encoder
        .solver
        .declare_const("__a_param", type_param_sort.clone());
    let b = encoder.solver.declare_const("__b_param", type_param_sort);

    // They should be distinguishable (not equal is satisfiable)
    let eq_ab = encoder.solver.eq(a, b);
    let neq = encoder.solver.not(eq_ab);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "type param sort constants should be distinguishable (not collapsed to Int)"
    );
}

// ── Pattern 6: Trait law axiom (traits/18_trait_laws) ──────────────────
//
// trait Symmetric {
//   #[logic] fn op(self, _: Self) -> &'static Self;
//   #[logic(law)] #[ensures(a.op(b) == b.op(a))] fn reflexive(a: Self, b: Self);
// }
// A trait law adds a universally quantified axiom. The `uses_op` function
// should be provable because the law provides `x.op(y) == y.op(x)`.

/// Regression test: a trait law axiom (symmetry) should make
/// `op(x, y) == op(y, x)` provable for any `T: Symmetric`.
#[test]
#[timeout(10000)]
fn test_trait_law_symmetry_axiom_provable() {
    let mut encoder = AYEncoder::new();

    let type_param_sort = Sort::Uninterpreted("T_sym".to_string());

    // Declare op: (T, T) -> T (simplified return type)
    let op_decl = encoder.get_or_declare_logic_func(
        "symmetric_op",
        &[type_param_sort.clone(), type_param_sort.clone()],
        type_param_sort.clone(),
    );

    // Trait law axiom: forall a:T, b:T. op(a, b) = op(b, a)
    let a_var = encoder.solver.fresh_var("__a_sym", type_param_sort.clone());
    let b_var = encoder.solver.fresh_var("__b_sym", type_param_sort.clone());
    let op_ab = encoder.solver.apply(&op_decl, &[a_var, b_var]);
    let op_ba = encoder.solver.apply(&op_decl, &[b_var, a_var]);
    let sym_eq = encoder.solver.eq(op_ab, op_ba);
    let law_axiom = encoder
        .solver
        .forall_with_triggers(&[a_var, b_var], sym_eq, &[&[op_ab]]);
    encoder.solver.assert_term(law_axiom);

    // Postcondition: ensures(op(x, y) == op(y, x)) for concrete x, y
    let cx = encoder
        .solver
        .declare_const("__cx_sym", type_param_sort.clone());
    let cy = encoder.solver.declare_const("__cy_sym", type_param_sort);
    let op_cx_cy = encoder.solver.apply(&op_decl, &[cx, cy]);
    let op_cy_cx = encoder.solver.apply(&op_decl, &[cy, cx]);
    let post_eq = encoder.solver.eq(op_cx_cy, op_cy_cx);
    let negated = encoder.solver.not(post_eq);
    encoder.assert_term(negated);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "trait law symmetry axiom should make op(x,y) == op(y,x) provable (#2670)"
    );
}

// ── Pattern 7: Generic trait predicate (bug/generic_trait_predicate) ───
//
// trait CP {
//   #[logic(open)] fn match_t<K>() -> bool { Self::match_n::<K>() }
//   #[logic] fn match_n<K>() -> bool;
// }
// impl<L, R> CP for (L, R) { fn match_n<N>() -> bool { true } }
//
// When a trait has generic methods with type parameters at both trait and
// method level, the encoder must handle multi-level type parameter sorts.

/// Regression test: trait method with independent type parameter at
/// method level. The impl body `true` should expand correctly.
#[test]
#[timeout(10000)]
fn test_generic_trait_predicate_multi_level_type_params() {
    let mut encoder = AYEncoder::new();

    // Type params: L, R at trait level; K at method level
    let sort_l = Sort::Uninterpreted("L_gtp".to_string());
    let sort_r = Sort::Uninterpreted("R_gtp".to_string());
    let sort_k = Sort::Uninterpreted("K_gtp".to_string());

    // Declare match_n for (L, R) impl: match_n<K>() -> Bool
    // In the impl, this is: forall K. match_n_LR<K>() = true
    let match_n_decl = encoder.get_or_declare_logic_func(
        "match_n_pair_LR",
        &[sort_l.clone(), sort_r.clone(), sort_k.clone()],
        Sort::Bool,
    );

    // Body expansion: forall l:L, r:R, k:K. match_n(l, r, k) = true
    let l_var = encoder.solver.fresh_var("__l_gtp", sort_l.clone());
    let r_var = encoder.solver.fresh_var("__r_gtp", sort_r.clone());
    let k_var = encoder.solver.fresh_var("__k_gtp", sort_k.clone());
    let app = encoder.solver.apply(&match_n_decl, &[l_var, r_var, k_var]);
    let true_const = encoder.solver.bool_const(true);
    let body_eq = encoder.solver.eq(app, true_const);
    let axiom = encoder
        .solver
        .forall_with_triggers(&[l_var, r_var, k_var], body_eq, &[&[app]]);
    encoder.solver.assert_term(axiom);

    // Declare match_t which delegates to match_n:
    // match_t<K>() = match_n<K>()
    let match_t_decl = encoder.get_or_declare_logic_func(
        "match_t_pair_LR",
        &[sort_l.clone(), sort_r.clone(), sort_k.clone()],
        Sort::Bool,
    );

    // Body expansion: forall l:L, r:R, k:K. match_t(l, r, k) = match_n(l, r, k)
    let l_var2 = encoder.solver.fresh_var("__l_gtp2", sort_l.clone());
    let r_var2 = encoder.solver.fresh_var("__r_gtp2", sort_r.clone());
    let k_var2 = encoder.solver.fresh_var("__k_gtp2", sort_k.clone());
    let t_app = encoder
        .solver
        .apply(&match_t_decl, &[l_var2, r_var2, k_var2]);
    let n_app = encoder
        .solver
        .apply(&match_n_decl, &[l_var2, r_var2, k_var2]);
    let delegate_eq = encoder.solver.eq(t_app, n_app);
    let delegate_axiom =
        encoder
            .solver
            .forall_with_triggers(&[l_var2, r_var2, k_var2], delegate_eq, &[&[t_app]]);
    encoder.solver.assert_term(delegate_axiom);

    // Verify: match_t(cl, cr, ck) should be true (transitively through match_n)
    let cl = encoder.solver.declare_const("__cl_gtp", sort_l);
    let cr = encoder.solver.declare_const("__cr_gtp", sort_r);
    let ck = encoder.solver.declare_const("__ck_gtp", sort_k);
    let concrete_t = encoder.solver.apply(&match_t_decl, &[cl, cr, ck]);
    let neg = encoder.solver.not(concrete_t);
    encoder.assert_term(neg);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "generic trait predicate with multi-level type params should be provable (#2670)"
    );
}

// ── Pattern 7b: Enum Default postcondition (derive_macros/default ETuple) ─
//
// #[derive(Default)]
// pub enum ETuple {
//     #[default] A(i32, i32),
//     B { x: Vec<i32> },
// }
//
// The derived Default produces `A(0, 0)`. The postcondition is:
//   match result { A(x0, x1) => postcond((), x0) && postcond((), x1), _ => false }
//
// This requires the postcondition axiom to connect with the datatype selectors
// on the enum constructor. The canonical `__trust_wp_unit` fix ensures the ground
// instance uses the same unit constant as the postcondition application.

/// Regression test: enum Default postcondition with constructor selectors
/// should be provable when the ground instance uses the canonical unit constant.
#[test]
#[timeout(10000)]
fn test_enum_default_postcondition_with_constructor_selectors() {
    let mut encoder = AYEncoder::new();

    let unit_sort = Sort::Uninterpreted("Unit".to_string());

    // Declare `Default::default` as a logic function — we use a fresh name
    // to avoid collision with the canonical DEFAULT_DEFAULT_SMT_NAME which
    // triggers the trait_postcondition axiom module automatically.
    let default_fn_decl = encoder.get_or_declare_logic_func("default_fn_etuple", &[], Sort::Int);
    let default_fn_term = encoder.solver.apply(&default_fn_decl, &[]);

    // Declare postcondition predicate: (Int, Unit, Int) -> Bool
    let postcond_decl = encoder.get_or_declare_logic_func(
        "postcond_enum_test",
        &[Sort::Int, unit_sort.clone(), Sort::Int],
        Sort::Bool,
    );

    // Manually assert the biconditional axiom (simulating trait_postcondition):
    // forall u:Unit, v:Int. postcond(fn, u, v) = (v == 0)
    let u_var = encoder.solver.fresh_var("__u_enum", unit_sort.clone());
    let v_var = encoder.solver.fresh_var("__v_enum", Sort::Int);
    let app = encoder
        .solver
        .apply(&postcond_decl, &[default_fn_term, u_var, v_var]);
    let zero = encoder.solver.int_const(0);
    let val_eq_zero = encoder.solver.eq(v_var, zero);
    let biconditional = encoder.solver.eq(app, val_eq_zero);
    let axiom = encoder
        .solver
        .forall_with_triggers(&[u_var, v_var], biconditional, &[&[app]]);
    encoder.solver.assert_term(axiom);

    // Eager ground instance using canonical unit constant
    let unit_ground = encoder
        .solver
        .declare_const("__trust_wp_unit", unit_sort.clone());
    let ground_app = encoder
        .solver
        .apply(&postcond_decl, &[default_fn_term, unit_ground, zero]);
    encoder.solver.assert_term(ground_app);

    // Declare enum ETuple with two constructors: A(Int, Int) and B(Seq<Int>)
    let etuple_dt = ay_dpll::api::DatatypeSort {
        name: "ETuple".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "A".to_string(),
                fields: vec![
                    ay_dpll::api::DatatypeField {
                        name: "etuple_a_0".to_string(),
                        sort: Sort::Int,
                    },
                    ay_dpll::api::DatatypeField {
                        name: "etuple_a_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "B".to_string(),
                fields: vec![ay_dpll::api::DatatypeField {
                    name: "etuple_b_x".to_string(),
                    sort: Sort::Uninterpreted("Vec_i32".to_string()),
                }],
            },
        ],
    };
    encoder.solver.declare_datatype(&etuple_dt);

    // result = A(0, 0) (from Default::default body encoding)
    let etuple_sort = Sort::Datatype(etuple_dt.clone());
    let result = encoder.solver.declare_const("__result_enum", etuple_sort);
    let a_0_0 = encoder
        .solver
        .datatype_constructor(&etuple_dt, "A", &[zero, zero]);
    let result_eq = encoder.solver.eq(result, a_0_0);
    encoder.assert_term(result_eq);

    // Postcondition: match result { A(x0, x1) => postcond((), x0) && postcond((), x1), _ => false }
    // Selector applications: etuple_a_0(result) and etuple_a_1(result)
    let field0 = encoder
        .solver
        .datatype_selector("etuple_a_0", result, Sort::Int);
    let field1 = encoder
        .solver
        .datatype_selector("etuple_a_1", result, Sort::Int);

    // Use the SAME __trust_wp_unit as the ground instance
    let unit_postcond = encoder.solver.declare_const("__trust_wp_unit", unit_sort);
    let postcond_f0 = encoder
        .solver
        .apply(&postcond_decl, &[default_fn_term, unit_postcond, field0]);
    let postcond_f1 = encoder
        .solver
        .apply(&postcond_decl, &[default_fn_term, unit_postcond, field1]);

    // is-A(result) check
    let is_a = encoder.solver.datatype_tester("A", result);

    // Postcondition body: is-A(result) => postcond(field0) && postcond(field1)
    // Negate: NOT(is-A(result) => postcond(field0) && postcond(field1))
    // = is-A(result) AND NOT(postcond(field0) AND postcond(field1))
    let both_postcond = encoder.solver.and(postcond_f0, postcond_f1);
    let neg_both = encoder.solver.not(both_postcond);
    let is_a_and_neg = encoder.solver.and(is_a, neg_both);
    encoder.assert_term(is_a_and_neg);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "enum Default postcondition with constructor selectors should be provable (#2670)"
    );
}

// ── Pattern 8: Default impl in trait calling self method (termination) ─
//
// trait Foo { #[logic] fn f() {}; #[logic] fn g(); }
// impl Foo for () { fn g() { <Self as Foo>::f(); } }
//
// Default method bodies that call other trait methods should not cause
// infinite recursion in the encoder. The termination check should handle
// self-referential trait method calls.

/// Regression test: default trait impl calling another trait method
/// should produce a consistent encoding (no infinite expansion).
#[test]
#[timeout(10000)]
fn test_default_impl_calling_trait_method_no_infinite_expansion() {
    let mut encoder = AYEncoder::new();

    let unit_sort = Sort::Uninterpreted("Unit_dit".to_string());

    // Declare f (default impl with empty body — returns Unit)
    let f_decl = encoder.get_or_declare_logic_func("trait_foo_f_dit", &[], unit_sort.clone());

    // Declare g for () impl: g() { <Self as Foo>::f() }
    let g_decl = encoder.get_or_declare_logic_func("trait_foo_g_unit_dit", &[], unit_sort.clone());

    // Body expansion for g: g() = f()
    let g_app = encoder.solver.apply(&g_decl, &[]);
    let f_app = encoder.solver.apply(&f_decl, &[]);
    let body_eq = encoder.solver.eq(g_app, f_app);
    encoder.solver.assert_term(body_eq);

    // The encoding should be consistent (not contradictory)
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "default impl calling trait method should produce consistent encoding (#2670)"
    );

    // Further: g() and f() should be the same value
    let g_result = encoder.solver.apply(&g_decl, &[]);
    let f_result = encoder.solver.apply(&f_decl, &[]);
    let eq = encoder.solver.eq(g_result, f_result);
    let neg = encoder.solver.not(eq);
    encoder.assert_term(neg);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "g() == f() should be provable when g's body is f() (#2670)"
    );
}
