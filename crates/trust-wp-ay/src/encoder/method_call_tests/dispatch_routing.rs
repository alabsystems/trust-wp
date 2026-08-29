// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

use super::*;
use crate::shared_types::UnknownReason;

fn assert_unsat_or_mixed_collection_unknown(
    encoder: &AYEncoder,
    result: &SolveResult,
    context: &str,
) {
    let mixed_collection_unknown = matches!(result, SolveResult::Unknown)
        && matches!(
            encoder.last_unknown_reason(),
            Some(UnknownReason::UnsupportedMixedCollection)
        );
    assert!(
        matches!(result, SolveResult::Unsat(_)) || mixed_collection_unknown,
        "{context}, got {result:?}; reason={:?}; executor_error={:?}",
        encoder.last_unknown_reason(),
        encoder.last_executor_error()
    );
}

#[test]
#[timeout(30000)]
fn index_on_bare_seq_sorted_var_uses_seq_dispatch_fallback() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let _ = encoder
        .get_or_declare_var("s_view", Sort::seq(Sort::Int))
        .expect("declare s_view: Seq");

    let result = encoder.encode_pure(&method_call(var("s_view"), "index", vec![int(0)]));
    assert!(
        result.is_ok(),
        "index on bare Seq-sorted Var should route to Seq encoding: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "Seq index fallback should initialize Seq functions"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_index_")),
        "Seq index fallback must not create generic method_index UF"
    );
}

#[test]
#[timeout(30000)]
fn get_on_bare_seq_sorted_var_uses_seq_dispatch_fallback() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let _ = encoder
        .get_or_declare_var("s_view", Sort::seq(Sort::Int))
        .expect("declare s_view: Seq");

    let result = encoder.encode_pure(&method_call(var("s_view"), "get", vec![int(0)]));
    assert!(
        result.is_ok(),
        "get on bare Seq-sorted Var should route to Seq encoding: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "Seq get fallback should initialize Seq functions"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_get_")),
        "Seq get fallback must not create generic method_get UF"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_on_bare_seq_sorted_var_uses_seq_dispatch_fallback() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let _ = encoder
        .get_or_declare_var("s_view", Sort::seq(Sort::Int))
        .expect("declare s_view: Seq");

    let result = encoder.encode_pure(&method_call(var("s_view"), "index_logic", vec![int(0)]));
    assert!(
        result.is_ok(),
        "index_logic on bare Seq-sorted Var should route to Seq encoding: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "Seq index_logic fallback should initialize Seq functions"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_")),
        "Seq index_logic fallback must not create generic method_index_logic UF"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_on_structural_field_receiver_reuses_seq_placeholder() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let expr = method_call(
        logic_fn_call("__trust_wp_tuple_get_0", vec![var("x")]),
        "index_logic",
        vec![int(0)],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "structural field index_logic should encode through the Seq lane: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "structural field index_logic should initialize the Seq theory"
    );
    assert!(
        !encoder.decls.has_spec_func("fmap_lookup"),
        "structural field index_logic must not route through fmap_lookup"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_")),
        "structural field index_logic must not create a generic method_index_logic UF"
    );
    assert!(
        encoder
            .seq_state
            .get_bridge_fn("__int_to_seq_bridge")
            .is_none(),
        "structural field index_logic should reuse a Seq placeholder, not the Int->Seq bridge"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_on_native_seq_field_receiver_uses_seq_dispatch() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "MyHashMap".to_string(),
        AdtDecl::new(
            "crate::MyHashMap".to_string(),
            "MyHashMap".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "MyHashMap".to_string(),
                "MyHashMap".to_string(),
                vec![AdtFieldDecl::new("buckets".to_string(), ExprSort::Seq)],
            )],
        ),
    )]));

    let self_sort = ExprSort::Datatype(intern_sort_name("crate::MyHashMap"));
    let expr = method_call(
        view(logic_fn_call(
            "myhashmap_buckets",
            vec![var_with_sort("self", self_sort)],
        )),
        "index_logic",
        vec![int(0)],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "native Seq field index_logic should route through Seq encoding: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "native Seq field index_logic should initialize the Seq theory"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_")),
        "native Seq field index_logic must not create a generic method_index_logic UF"
    );
}

#[test]
#[timeout(30000)]
fn get_on_view_frag_field_uses_fmap_dispatch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let receiver = named_field("frag", view(var("resource")));

    assert_eq!(
        encoder.infer_expr_sort_with_context(&receiver, None),
        Sort::Uninterpreted("FMap".to_string()),
        "frag field receiver should infer as FMap before method dispatch"
    );

    let result = encoder.encode_pure(&method_call(receiver, "get", vec![var("k")]));
    assert!(
        result.is_ok(),
        "get on a view fragment field should route through FMap encoding: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_lookup"),
        "frag field receiver should create fmap_lookup"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_get_")),
        "frag field receiver must not create a generic method_get UF"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_on_native_seq_field_uses_encoded_int_key_over_stale_seq_hint() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "MyHashMap".to_string(),
        AdtDecl::new(
            "crate::MyHashMap".to_string(),
            "MyHashMap".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "MyHashMap".to_string(),
                "MyHashMap".to_string(),
                vec![AdtFieldDecl::new("buckets".to_string(), ExprSort::Seq)],
            )],
        ),
    )]));

    let hashmap_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::MyHashMap")));
    encoder
        .get_or_declare_var("self_current", hashmap_sort)
        .expect("declare self_current as MyHashMap");
    encoder
        .get_or_declare_var("i", Sort::Int)
        .expect("declare i as Int");
    encoder.record_sort_hint("i".to_string(), ExprSort::Seq);

    let expr = method_call(
        logic_fn_call("myhashmap_buckets", vec![var("self_current")]),
        "index_logic",
        vec![var("i")],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "native Seq field index_logic should honor the encoded Int key: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "native Seq field index_logic should initialize the Seq theory"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_")),
        "native Seq field index_logic must not create a generic method_index_logic UF"
    );
}

#[test]
#[timeout(30000)]
fn len_on_native_seq_field_receiver_uses_encoded_seq_sort() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "MyHashMap".to_string(),
        AdtDecl::new(
            "crate::MyHashMap".to_string(),
            "MyHashMap".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "MyHashMap".to_string(),
                "MyHashMap".to_string(),
                vec![AdtFieldDecl::new("buckets".to_string(), ExprSort::Seq)],
            )],
        ),
    )]));

    let hashmap_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::MyHashMap")));
    encoder
        .get_or_declare_var("self_current_final", hashmap_sort)
        .expect("declare self_current_final as MyHashMap");

    let expr = method_call(
        logic_fn_call("myhashmap_buckets", vec![var("self_current_final")]),
        "len",
        vec![],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "native Seq field len should route through Seq encoding: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "native Seq field len should initialize the Seq theory"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_len_")),
        "native Seq field len must not create a generic method_len UF"
    );
}

#[test]
#[timeout(30000)]
fn qualified_logic_method_suffix_dispatch_avoids_generic_method_uf() {
    let mut encoder = AYEncoder::new();
    let hashmap_sort = Sort::Uninterpreted("MyHashMap".to_string());
    let list_sort = Sort::Uninterpreted("List".to_string());
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("creusot_test::MyHashMap::good_bucket");
    let decl = encoder.solver_mut().declare_fun(
        &smt_name,
        &[hashmap_sort.clone(), list_sort.clone(), Sort::Int],
        Sort::Bool,
    );
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, decl);
    encoder
        .get_or_declare_var("self", hashmap_sort)
        .expect("declare self as MyHashMap");
    encoder
        .get_or_declare_var("bucket", list_sort)
        .expect("declare bucket as List");

    let result = encoder.encode_pure(&method_call(
        var("self"),
        "good_bucket",
        vec![var("bucket"), int(0)],
    ));

    assert!(
        result.is_ok(),
        "qualified impl logic method should dispatch by method-name suffix: {result:?}"
    );
    assert_eq!(encoder.solver.get_sort(result.unwrap()), Sort::Bool);
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_good_bucket_")),
        "qualified logic method dispatch must not create a generic method_good_bucket UF"
    );
}

#[test]
#[timeout(30000)]
fn len_on_structural_field_receiver_uses_seq_placeholder_before_tuple_get_encoding() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let mut encoder = AYEncoder::new_all();
    let decls = std::collections::HashMap::from([
        (
            "List".to_string(),
            AdtDecl::new(
                "crate::List".to_string(),
                "List".to_string(),
                AdtKind::Enum,
                vec![
                    AdtConstructorDecl::new("List::Nil".to_string(), "Nil".to_string(), vec![]),
                    AdtConstructorDecl::new(
                        "List::Cons".to_string(),
                        "Cons".to_string(),
                        vec![AdtFieldDecl::new("head".to_string(), ExprSort::Int)],
                    ),
                ],
            ),
        ),
        (
            "MyHashMap".to_string(),
            AdtDecl::new(
                "crate::MyHashMap".to_string(),
                "MyHashMap".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "MyHashMap".to_string(),
                    "MyHashMap".to_string(),
                    vec![AdtFieldDecl::new("buckets".to_string(), ExprSort::Seq)],
                )],
            ),
        ),
    ]);
    encoder.register_adt_decls(&decls);

    let hashmap_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::MyHashMap")));
    encoder
        .get_or_declare_var("self", hashmap_sort)
        .expect("declare self as MyHashMap");

    let contaminated_self =
        var_with_sort("self", ExprSort::Datatype(intern_sort_name("crate::List")));
    let expr = method_call(
        view(logic_fn_call(
            "__trust_wp_tuple_get_0",
            vec![contaminated_self],
        )),
        "len",
        vec![],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "structural field len should use the Seq placeholder before stale tuple_get sort metadata can fire: {result:?}"
    );
    assert_eq!(encoder.solver.get_sort(result.unwrap()), Sort::Int);
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "structural field len must not declare or apply the bare tuple-get UF"
    );
}

#[test]
#[timeout(30000)]
fn unknown_method_inside_quantifier_scope_falls_back_to_int_uf() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let expr = forall_with_sort(
        "x",
        ExprSort::Int,
        eq(method_call(var("x"), "totally_unknown", vec![]), int(0)),
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "unknown methods inside quantified bodies should encode via Int UF fallback: {result:?}"
    );
    assert!(
        encoder.decls.has_logic_func("method_totally_unknown_1_i"),
        "quantified unknown method should declare the Int UF fallback"
    );
}

/// Known methods in the dispatch table still encode correctly (#1820).
#[test]
#[timeout(30000)]
fn known_methods_still_encode() {
    let mut encoder = AYEncoder::new();

    // deep_model is explicitly dispatched to encode_int_method_uf
    let expr = method_call(var("x"), "deep_model", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "known method deep_model should still encode: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn range_log_accessors_encode_as_int_ufs() {
    let mut encoder = AYEncoder::new();

    let start = method_call(var("range_iter"), "start_log", vec![]);
    let end = method_call(var("range_iter"), "end_log", vec![]);

    let start_term = encoder
        .encode_pure(&start)
        .expect("start_log should encode as an Int-returning UF");
    let end_term = encoder
        .encode_pure(&end)
        .expect("end_log should encode as an Int-returning UF");

    assert!(
        encoder.decls.has_logic_func("method_start_log_1_i"),
        "start_log should declare method_start_log_1_i"
    );
    assert!(
        encoder.decls.has_logic_func("method_end_log_1_i"),
        "end_log should declare method_end_log_1_i"
    );

    let eq = encoder.solver.eq(start_term, end_term);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "range log accessor UFs should participate in Int equalities"
    );
}

#[test]
#[timeout(30000)]
fn rem_euclid_routes_to_modulo_encoder() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(int(17), "rem_euclid", vec![int(5)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("rem_euclid should encode via modulo");

    assert_eq!(encoder.solver.get_sort(term), Sort::Int);
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_rem_euclid_")),
        "rem_euclid should use modulo encoding, not a method UF"
    );
}

#[test]
#[timeout(30000)]
fn range_log_accessors_infer_int_sort_for_mutref_range_receivers() {
    unsoundness::reset();
    let mut encoder = AYEncoder::new();
    let range_sort = ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name(
        "core::ops::range::Range",
    ))));
    let receiver = PureExpr::Var("range_iter".to_string(), Some(range_sort));
    let start = method_call(receiver.clone(), "start_log", vec![]);
    let end = method_call(receiver, "end_log", vec![]);

    let before = unsoundness::snapshot();
    let start_sort = encoder.infer_expr_sort_with_context(&start, None);
    let end_sort = encoder.infer_expr_sort_with_context(&end, None);
    let after = unsoundness::snapshot();
    let fallback_delta = unsoundness::delta(&before, &after);

    assert_eq!(
        start_sort,
        Sort::Int,
        "start_log should infer as Int for MutRef<Range> receivers"
    );
    assert_eq!(
        end_sort,
        Sort::Int,
        "end_log should infer as Int for MutRef<Range> receivers"
    );
    assert_eq!(
        fallback_delta.get(&UnsoundnessCategory::SortFallbackToInt),
        None,
        "range log accessors should not hit generic sort fallback: {fallback_delta:?}"
    );
}

/// A user-defined Bool-returning logic function called in method syntax
/// (receiver.is_valid()) is encoded with Bool sort, not Int (#1820 AC-2/AC-3).
///
/// Before #1820, unknown methods silently created Int-returning UFs. Now:
/// 1. Registered logic functions are routed through the logic_fn encoder
///    which infers Sort::Bool from the body.
/// 2. Unregistered methods produce EncodingError.
///
/// This test registers `is_valid(x) := x > 0` (returns Bool), then calls
/// it as `receiver.is_valid()` and verifies the result is usable in Bool
/// contexts (negation, conjunction).
#[test]
#[timeout(30000)]
fn user_defined_bool_logic_fn_via_method_syntax() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    use crate::tests::helpers::gt;

    let mut encoder = AYEncoder::new();

    // Register: is_valid(x) := x > 0  (Bool body)
    let logic_fn = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("register is_valid");

    // Encode: receiver.is_valid() in method syntax — dispatched to
    // the logic_fn fallback path (not built-in methods).
    let expr = method_call(var("receiver"), "is_valid", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("registered Bool logic fn should encode via method syntax");

    // The result must be Bool-sorted: negation should be valid.
    let negated = encoder.solver.not(term);
    encoder.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "negated Bool UF should be satisfiable: {result:?}"
    );
}

/// FMap `contains` creates `fmap_contains` when receiver has FMap sort hint (#1778).
///
/// Before this fix, non-Seq `contains` always routed to FSet dispatch,
/// creating `fset_contains` even for FMap receivers. With an FMap sort
/// hint from prescan (e.g., from seeing `receiver.lookup(k)`), the
/// dispatch now correctly routes to `encode_fmap_method`.
#[test]
#[timeout(30000)]
fn fmap_contains_routes_to_fmap_encoding() {
    let mut encoder = AYEncoder::new();
    // Simulate prescan: tag "m" as FMap-sorted (as if `m.lookup(k)` was seen)
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let expr = method_call(var("m"), "contains", vec![var("k")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap contains should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_contains"),
        "FMap receiver should create fmap_contains, not fset_contains"
    );
    assert!(
        !encoder.decls.has_spec_func("fset_contains"),
        "FMap receiver should NOT create fset_contains"
    );
}

/// FSet `contains` still routes to FSet encoding when receiver has no FMap hint (#1778).
#[test]
#[timeout(30000)]
fn fset_contains_unchanged_without_fmap_hint() {
    let mut encoder = AYEncoder::new();
    // No FMap or Seq sort hint — should default to FSet
    let expr = method_call(var("s"), "contains", vec![var("elem")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FSet contains should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fset_contains"),
        "non-FMap, non-Seq receiver should create fset_contains"
    );
    assert!(
        !encoder.decls.has_spec_func("fmap_contains"),
        "non-FMap receiver should NOT create fmap_contains"
    );
}

/// FMap `insert` routes to FMap encoding via explicit dispatch (#1778).
#[test]
#[timeout(30000)]
fn fmap_insert_routes_to_fmap_encoding() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("m"), "insert", vec![var("k"), var("v")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap insert should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_insert"),
        "insert(key, value) should create fmap_insert"
    );
}

#[test]
#[timeout(30000)]
fn fmap_insert_accepts_seq_value_sort() {
    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let perm_cell = Sort::Uninterpreted("PermCell".to_string());
    let _ = encoder
        .get_or_declare_var("m", fmap)
        .expect("declare m FMap");
    let _ = encoder
        .get_or_declare_var("k_perm", perm_cell)
        .expect("declare k_perm PermCell");
    let _ = encoder
        .get_or_declare_var("v_seq", Sort::seq(Sort::Int))
        .expect("declare v_seq Seq");

    let expr = method_call(var("m"), "insert", vec![var("k_perm"), var("v_seq")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap insert should accept non-Int value payloads: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_insert"),
        "insert(key, seq_value) should still create fmap_insert"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_insert_")),
        "Seq-valued FMap insert must not fall back to generic method_insert"
    );
}

/// FMap `into_seq` routes to FMap encoding and creates `fmap_into_seq`.
#[test]
#[timeout(30000)]
fn fmap_into_seq_routes_to_fmap_encoding() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var_with_sort("m", ExprSort::FMap), "into_seq", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap into_seq should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_into_seq"),
        "into_seq() should create fmap_into_seq"
    );
    assert_eq!(
        encoder
            .solver
            .get_sort(result.expect("fmap_into_seq result")),
        Sort::seq(Sort::Int),
        "into_seq() should return Seq<Int>"
    );
}

/// FMap `insert_ghost` is an alias for `insert` in the dispatch (#1778).
#[test]
#[timeout(30000)]
fn fmap_insert_ghost_routes_to_fmap_encoding() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("m"), "insert_ghost", vec![var("k"), var("v")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap insert_ghost should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_insert"),
        "insert_ghost(key, value) should create fmap_insert"
    );
}

#[test]
#[timeout(30000)]
fn fmap_insert_local_update_premise_routes_to_fmap_contains() {
    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let perm_cell = Sort::Uninterpreted("PermCell".to_string());
    let _ = encoder
        .get_or_declare_var("auth", fmap.clone())
        .expect("declare auth FMap");
    let _ = encoder
        .get_or_declare_var("frag", fmap)
        .expect("declare frag FMap");
    let _ = encoder
        .get_or_declare_var("k_perm", perm_cell)
        .expect("declare k_perm PermCell");
    let upd = logic_fn_call("__trust_wp_tuple2", vec![var("k_perm"), var("v")]);
    let expr = method_call(upd, "premise", vec![var("auth"), var("frag")]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMapInsertLocalUpdate::premise should encode: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_contains"),
        "premise should reduce to fmap_contains"
    );
}

#[test]
#[timeout(30000)]
fn fmap_insert_local_update_update_routes_to_paired_fmap_insert() {
    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let perm_cell = Sort::Uninterpreted("PermCell".to_string());
    let _ = encoder
        .get_or_declare_var("auth", fmap.clone())
        .expect("declare auth FMap");
    let _ = encoder
        .get_or_declare_var("frag", fmap)
        .expect("declare frag FMap");
    let _ = encoder
        .get_or_declare_var("k_perm", perm_cell)
        .expect("declare k_perm PermCell");
    let _ = encoder
        .get_or_declare_var("v_seq", Sort::seq(Sort::Int))
        .expect("declare v_seq Seq");
    let upd = logic_fn_call("__trust_wp_tuple2", vec![var("k_perm"), var("v_seq")]);
    let expr = method_call(upd, "update", vec![var("auth"), var("frag")]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMapInsertLocalUpdate::update should encode: {result:?}"
    );
    let term = result.expect("checked ok");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Uninterpreted("Tuple2".to_string())
    );
    assert!(
        encoder.decls.has_spec_func("fmap_insert"),
        "update should reduce both outputs to fmap_insert terms"
    );
}

#[test]
#[timeout(30000)]
fn fmap_lookup_preserves_inserted_value_sort() {
    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("m", fmap)
        .expect("declare m FMap");
    encoder
        .get_or_declare_var("v_seq", Sort::seq(Sort::Int))
        .expect("declare v_seq Seq");

    let inserted = method_call(var("m"), "insert", vec![var("k"), var("v_seq")]);
    let lookup = method_call(inserted, "lookup", vec![var("k")]);
    let term = encoder
        .encode_pure(&lookup)
        .expect("lookup after insert should encode");

    assert!(
        encoder.solver.get_sort(term).is_seq(),
        "lookup(insert(m, k, v_seq), k) should carry the inserted Seq value sort"
    );
}

#[test]
#[timeout(30000)]
fn fmap_get_unwrap_logic_routes_to_value_lookup() {
    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("m", fmap)
        .expect("declare m FMap");
    encoder
        .get_or_declare_var("v_seq", Sort::seq(Sort::Int))
        .expect("declare v_seq Seq");

    let inserted = method_call(var("m"), "insert", vec![var("k"), var("v_seq")]);
    let get = method_call(inserted, "get", vec![var("k")]);
    let unwrap = method_call(get, "unwrap_logic", vec![]);
    let term = encoder
        .encode_pure(&unwrap)
        .expect("get(...).unwrap_logic() should encode as FMap lookup");

    assert!(
        encoder.solver.get_sort(term).is_seq(),
        "FMap get(...).unwrap_logic() should carry the map value sort"
    );
    assert!(
        !encoder.decls.has_spec_func("spec_unwrap"),
        "FMap get unwrap should not go through the generic Option unwrap UF"
    );
}

#[test]
#[timeout(30000)]
fn fmap_local_update_result_equality_preseeds_final_view_hint() {
    let mut encoder = AYEncoder::new();
    let update = method_call(
        logic_fn_call(
            "__trust_wp_tuple2",
            vec![var("perm_cell"), var_with_sort("new_value", ExprSort::Seq)],
        ),
        "update",
        vec![view(var("auth")), view(var("frag"))],
    );
    let equality = eq(
        view(final_expr(var("auth"))),
        logic_fn_call("__trust_wp_tuple_get_0", vec![update]),
    );

    let encoded = encoder
        .encode_pure(&equality)
        .expect("local-update result equality should encode");

    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);
    assert!(
        encoder.sort_hint_matches("final_auth_view", &ExprSort::FMap),
        "Authority::update final self view should be seeded as FMap"
    );
}

#[test]
#[timeout(30000)]
fn fmap_local_update_result_equality_preseeds_value_sort_hint() {
    let mut encoder = AYEncoder::new();
    let update = method_call(
        logic_fn_call(
            "__trust_wp_tuple2",
            vec![var("perm_cell"), var_with_sort("new_value", ExprSort::Seq)],
        ),
        "update",
        vec![view(var("auth")), view(var("frag"))],
    );
    let equality = eq(
        view(final_expr(var("frag"))),
        logic_fn_call("__trust_wp_tuple_get_1", vec![update]),
    );

    let encoded = encoder
        .encode_pure(&equality)
        .expect("local-update result equality should encode");

    assert_eq!(encoder.solver.get_sort(encoded), Sort::Bool);
    assert!(
        encoder
            .encoding_cache
            .fmap_value_sort_name("final_frag_view")
            .is_some_and(|sort| sort.is_seq()),
        "Authority::update final fragment view should remember the inserted value sort"
    );
}

#[test]
#[timeout(30000)]
fn fmap_local_update_output_equality_rewrites_to_insert_alias() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("auth_view", fmap.clone())
        .expect("declare auth view");
    encoder
        .get_or_declare_var("frag_view", fmap.clone())
        .expect("declare frag view");
    encoder
        .get_or_declare_var("final_frag_view", fmap)
        .expect("declare final frag view");
    encoder
        .get_or_declare_var("key", Sort::Int)
        .expect("declare key");
    encoder
        .get_or_declare_var("v_seq", Sort::seq(Sort::Int))
        .expect("declare Seq payload");

    let update = method_call(
        logic_fn_call("__trust_wp_tuple2", vec![var("key"), var("v_seq")]),
        "update",
        vec![var("auth_view"), var("frag_view")],
    );
    let final_frag_eq = eq(
        var("final_frag_view"),
        logic_fn_call("__trust_wp_tuple_get_1", vec![update]),
    );
    let lookup = method_call(var("final_frag_view"), "lookup", vec![var("key")]);
    let payload_eq = eq(lookup, var("v_seq"));

    let final_frag_eq = encoder
        .encode_pure(&final_frag_eq)
        .expect("local update output equality should encode");
    encoder.assert_term(final_frag_eq);
    let payload_eq = encoder
        .encode_pure(&payload_eq)
        .expect("final fragment lookup equality should encode");
    encoder.assert_standard_ground_instances();
    let not_payload_eq = encoder.solver.not(payload_eq);
    encoder.assert_term(not_payload_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "local-update output equality should directly expose the corresponding fmap_insert alias, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn fmap_local_update_final_view_lookup_exposes_inserted_payload() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("auth_view", fmap.clone())
        .expect("declare auth view");
    encoder
        .get_or_declare_var("frag_view", fmap.clone())
        .expect("declare frag view");
    encoder
        .get_or_declare_var("final_frag_view", fmap)
        .expect("declare final frag view");
    encoder
        .get_or_declare_var("key", Sort::Int)
        .expect("declare key");
    encoder
        .get_or_declare_var("v_seq", Sort::seq(Sort::Int))
        .expect("declare Seq payload");

    let ag_value = logic_fn_call("__trust_wp_tuple1", vec![var("v_seq")]);
    let update = method_call(
        logic_fn_call("__trust_wp_tuple2", vec![var("key"), ag_value.clone()]),
        "update",
        vec![var("auth_view"), var("frag_view")],
    );
    let final_frag_eq = eq(
        var("final_frag_view"),
        logic_fn_call("__trust_wp_tuple_get_1", vec![update]),
    );
    let get = method_call(var("final_frag_view"), "get", vec![var("key")]);
    let payload = logic_fn_call(
        "__trust_wp_tuple_get_0",
        vec![method_call(get, "unwrap_logic", vec![])],
    );
    let payload_eq = eq(payload, var("v_seq"));

    let final_frag_eq = encoder
        .encode_pure(&final_frag_eq)
        .expect("local update equality should encode");
    encoder.assert_term(final_frag_eq);
    let payload_eq = encoder
        .encode_pure(&payload_eq)
        .expect("payload equality should encode");
    encoder.assert_tuple_axioms();
    encoder.assert_standard_ground_instances();
    let not_payload_eq = encoder.solver.not(payload_eq);
    encoder.assert_term(not_payload_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "local-update final view lookup should expose the inserted tuple payload, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn fmap_local_update_value_sort_preserves_datatype_payload_axioms() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq = Sort::seq(Sort::Int);
    let ag = DatatypeSort {
        name: "Ag".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ag".to_string(),
            fields: vec![DatatypeField {
                name: "ag_0".to_string(),
                sort: seq.clone(),
            }],
        }],
    };
    encoder.ensure_datatype_declared(&ag);
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("auth_view", fmap.clone())
        .expect("declare auth view");
    encoder
        .get_or_declare_var("frag_view", fmap.clone())
        .expect("declare frag view");
    encoder
        .get_or_declare_var("final_frag_view", fmap)
        .expect("declare final frag view");
    encoder
        .get_or_declare_var("key", Sort::Int)
        .expect("declare key");
    encoder
        .get_or_declare_var("v_seq", seq)
        .expect("declare Seq payload");

    let ag_value = var_with_sort("ag", ExprSort::Datatype(intern_sort_name("Ag")));
    let ag_constructor = logic_fn_call("Ag", vec![var("v_seq")]);
    let ag_eq = eq(ag_value.clone(), ag_constructor);
    let update = method_call(
        logic_fn_call("__trust_wp_tuple2", vec![var("key"), ag_value]),
        "update",
        vec![var("auth_view"), var("frag_view")],
    );
    let final_frag_eq = eq(
        var("final_frag_view"),
        logic_fn_call("__trust_wp_tuple_get_1", vec![update]),
    );
    let get = method_call(var("final_frag_view"), "get", vec![var("key")]);
    let get_unwrap = method_call(get.clone(), "unwrap_logic", vec![]);
    let payload = logic_fn_call("__trust_wp_tuple_get_0", vec![get_unwrap.clone()]);
    let payload_eq = eq(payload.clone(), var("v_seq"));

    let ag_eq = encoder
        .encode_pure(&ag_eq)
        .expect("Ag constructor equality should encode");
    encoder.assert_term(ag_eq);
    let final_frag_eq = encoder
        .encode_pure(&final_frag_eq)
        .expect("local update equality should encode");
    encoder.assert_term(final_frag_eq);
    assert!(
        matches!(
            encoder
                .encoding_cache
                .fmap_value_sort_name("final_frag_view"),
            Some(Sort::Datatype(dt)) if dt.name == "Ag"
        ),
        "local-update preseed should keep the native Ag datatype sort"
    );
    let payload_eq = encoder
        .encode_pure(&payload_eq)
        .expect("payload equality should encode");
    encoder.assert_tuple_axioms();
    encoder.assert_standard_ground_instances();
    let not_payload_eq = encoder.solver.not(payload_eq);
    encoder.assert_term(not_payload_eq);

    let result = encoder.check_sat();
    assert_unsat_or_mixed_collection_unknown(
        &encoder,
        &result,
        "datatype-valued local-update lookup should expose the inserted payload or fail closed on ay mixed-collection support",
    );
}

#[test]
#[timeout(30000)]
fn fmap_local_update_view_final_lookup_uses_value_sort_hint() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq = Sort::seq(Sort::Int);
    let ag = DatatypeSort {
        name: "Ag".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ag".to_string(),
            fields: vec![DatatypeField {
                name: "ag_0".to_string(),
                sort: seq.clone(),
            }],
        }],
    };
    encoder.ensure_datatype_declared(&ag);
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("auth_view", fmap.clone())
        .expect("declare auth view");
    encoder
        .get_or_declare_var("frag_view", fmap)
        .expect("declare frag view");
    encoder
        .get_or_declare_var("key", Sort::Int)
        .expect("declare key");
    encoder
        .get_or_declare_var("v_seq", seq)
        .expect("declare Seq payload");

    let ag_value = var_with_sort("ag", ExprSort::Datatype(intern_sort_name("Ag")));
    let ag_constructor = logic_fn_call("Ag", vec![var("v_seq")]);
    let ag_eq = eq(ag_value.clone(), ag_constructor);
    let update = method_call(
        logic_fn_call("__trust_wp_tuple2", vec![var("key"), ag_value]),
        "update",
        vec![var("auth_view"), view(var("frag"))],
    );
    let final_frag_eq = eq(
        view(final_expr(var("frag"))),
        logic_fn_call("__trust_wp_tuple_get_1", vec![update]),
    );
    let get = method_call(view(final_expr(var("frag"))), "get", vec![var("key")]);
    let get_unwrap = method_call(get, "unwrap_logic", vec![]);

    let ag_eq = encoder
        .encode_pure(&ag_eq)
        .expect("Ag constructor equality should encode");
    encoder.assert_term(ag_eq);
    let final_frag_eq = encoder
        .encode_pure(&final_frag_eq)
        .expect("local update equality should encode");
    encoder.assert_term(final_frag_eq);
    assert!(
        matches!(
            encoder
                .encoding_cache
                .fmap_value_sort_name("final_frag_view"),
            Some(Sort::Datatype(dt)) if dt.name == "Ag"
        ),
        "View(Final(frag)) local-update preseed should record the final view value sort"
    );

    let lookup_term = encoder
        .encode_pure(&get_unwrap)
        .expect("final view lookup unwrap should encode");
    let lookup_sort = encoder.solver.get_sort(lookup_term);
    assert!(
        matches!(&lookup_sort, Sort::Uninterpreted(name) if name == "Ag")
            || matches!(&lookup_sort, Sort::Datatype(dt) if dt.name == "Ag"),
        "View(Final(frag)).get(...).unwrap_logic() should use the cached Ag value sort, got {lookup_sort:?}"
    );

    let payload = logic_fn_call("__trust_wp_tuple_get_0", vec![get_unwrap]);
    let payload_eq = encoder
        .encode_pure(&eq(payload, var("v_seq")))
        .expect("wrapped final view payload equality should encode");
    encoder.assert_tuple_axioms();
    encoder.assert_standard_ground_instances();
    let not_payload_eq = encoder.solver.not(payload_eq);
    encoder.assert_term(not_payload_eq);

    let result = encoder.check_sat();
    assert_unsat_or_mixed_collection_unknown(
        &encoder,
        &result,
        "View(Final(frag)) lookup projection should expose the inserted payload or fail closed on ay mixed-collection support",
    );
}

#[test]
#[timeout(30000)]
fn single_field_constructor_equality_exposes_erased_payload_alias() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq = Sort::seq(Sort::Int);
    let ag = DatatypeSort {
        name: "Ag".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ag".to_string(),
            fields: vec![DatatypeField {
                name: "ag_0".to_string(),
                sort: seq.clone(),
            }],
        }],
    };
    encoder.ensure_datatype_declared(&ag);
    encoder
        .get_or_declare_var("v_seq", seq.clone())
        .expect("declare Seq payload");
    encoder
        .get_or_declare_var("new_ag", seq)
        .expect("declare erased Ag alias as Seq");

    let ag_eq = eq(logic_fn_call("Ag", vec![var("v_seq")]), var("new_ag"));
    let alias_eq = eq(var("new_ag"), var("v_seq"));
    let ag_eq = encoder
        .encode_pure(&ag_eq)
        .expect("Ag constructor alias equality should encode");
    encoder.assert_term(ag_eq);
    let alias_eq = encoder
        .encode_pure(&alias_eq)
        .expect("payload alias equality should encode");
    let not_alias_eq = encoder.solver.not(alias_eq);
    encoder.assert_term(not_alias_eq);

    let result = encoder.check_sat();
    assert_unsat_or_mixed_collection_unknown(
        &encoder,
        &result,
        "single-field constructor equality should expose erased payload alias or fail closed on ay mixed-collection support",
    );
}

/// FMap `merge` routes to FMap encoding and creates `fmap_merge` (#1778).
#[test]
#[timeout(30000)]
fn fmap_merge_routes_to_fmap_encoding() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("m1"), "merge", vec![var("m2"), var("resolver")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FMap merge should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fmap_merge"),
        "merge(other, resolver) should create fmap_merge"
    );
}

/// FSet `insert` (1-arg) routes to FSet encoding via arity dispatch (#1581).
#[test]
#[timeout(30000)]
fn fset_insert_routes_to_fset_encoding() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("s"), "insert", vec![var("elem")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FSet insert should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fset_insert"),
        "insert(elem) should create fset_insert"
    );
}

/// FSet `insert_ghost` (1-arg) is an alias for `insert` in the dispatch (#1581).
#[test]
#[timeout(30000)]
fn fset_insert_ghost_routes_to_fset_encoding() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("s"), "insert_ghost", vec![var("elem")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "FSet insert_ghost should encode successfully: {result:?}"
    );
    assert!(
        encoder.decls.has_spec_func("fset_insert"),
        "insert_ghost(elem) should create fset_insert"
    );
}
