// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort};

use super::*;

#[test]
#[timeout(30000)]
fn test_vec_datatype_maps_to_seq() {
    let id = intern_sort_name("std::vec::Vec");
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(id));
    assert_eq!(sort, Sort::seq(Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_ref_vec_datatype_maps_to_seq() {
    let id = intern_sort_name("std::vec::Vec");
    let sort = expr_sort_to_ay_sort(&ExprSort::Ref(Box::new(ExprSort::Datatype(id))));
    assert_eq!(sort, Sort::seq(Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_creusot_seq_datatype_maps_to_seq() {
    let id = intern_sort_name("creusot_std::Seq");
    let seq = Sort::seq(Sort::Int);
    assert_eq!(expr_sort_to_ay_sort(&ExprSort::Datatype(id)), seq);
}

#[test]
#[timeout(30000)]
fn test_bare_seq_datatype_maps_to_seq() {
    let seq = Sort::seq(Sort::Int);
    let id = intern_sort_name("Seq");
    assert_eq!(expr_sort_to_ay_sort(&ExprSort::Datatype(id)), seq);
}

#[test]
#[timeout(30000)]
fn test_non_collection_datatype_strips_to_bare_name() {
    let id = intern_sort_name("my::Custom");
    assert_eq!(
        expr_sort_to_ay_sort(&ExprSort::Datatype(id)),
        Sort::Uninterpreted("Custom".to_string()),
    );
}

#[test]
#[timeout(30000)]
fn test_duration_datatype_maps_to_int() {
    let id = intern_sort_name("std::time::Duration");
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(id));
    assert_eq!(sort, Sort::Int, "Duration should model as Int");
}

#[test]
#[timeout(30000)]
fn test_instant_datatype_maps_to_int() {
    let id = intern_sort_name("std::time::Instant");
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(id));
    assert_eq!(sort, Sort::Int, "Instant should model as Int");
}

#[test]
#[timeout(30000)]
fn test_ghost_datatype_maps_to_int() {
    let id = intern_sort_name("creusot_std::Ghost");
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(id));
    assert_eq!(sort, Sort::Int, "Ghost should model as Int");
}

#[test]
#[timeout(30000)]
fn test_creusot_int_datatype_maps_to_int() {
    let id = intern_sort_name("creusot_std::Int");
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(id));
    assert_eq!(sort, Sort::Int, "creusot_std::Int should model as Int");
}

#[test]
#[timeout(30000)]
fn test_ref_duration_datatype_maps_to_int() {
    let id = intern_sort_name("std::time::Duration");
    let sort = expr_sort_to_ay_sort(&ExprSort::Ref(Box::new(ExprSort::Datatype(id))));
    assert_eq!(sort, Sort::Int, "Ref(Duration) should model as Int");
}

#[test]
#[timeout(30000)]
fn test_canonical_sort_seq_types() {
    assert_eq!(canonical_sort("Vec"), CanonicalSort::Seq);
    assert_eq!(canonical_sort("Seq"), CanonicalSort::Seq);
    assert_eq!(canonical_sort("VecDeque"), CanonicalSort::Seq);
    assert_eq!(canonical_sort("std::vec::Vec"), CanonicalSort::Seq);
    assert_eq!(canonical_sort("creusot_std::Seq"), CanonicalSort::Seq);
}

#[test]
#[timeout(30000)]
fn test_canonical_sort_fmap_types() {
    assert_eq!(canonical_sort("FMap"), CanonicalSort::FMap);
    assert_eq!(canonical_sort("HashMap"), CanonicalSort::FMap);
    assert_eq!(canonical_sort("GhostMap"), CanonicalSort::FMap);
    assert_eq!(
        canonical_sort("std::collections::HashMap"),
        CanonicalSort::FMap
    );
}

#[test]
#[timeout(30000)]
fn test_canonical_sort_int_types() {
    assert_eq!(canonical_sort("Ghost"), CanonicalSort::Int);
    assert_eq!(canonical_sort("Int"), CanonicalSort::Int);
    assert_eq!(canonical_sort("Snapshot"), CanonicalSort::Int);
    assert_eq!(canonical_sort("Duration"), CanonicalSort::Int);
    assert_eq!(canonical_sort("HashSet"), CanonicalSort::Int);
    assert_eq!(canonical_sort("FSet"), CanonicalSort::Int);
    assert_eq!(canonical_sort("NonZeroU64"), CanonicalSort::Int);
    assert_eq!(canonical_sort("std::time::Duration"), CanonicalSort::Int);
}

#[test]
#[timeout(30000)]
fn test_canonical_sort_uninterpreted_types() {
    assert_eq!(
        canonical_sort("MyCustomType"),
        CanonicalSort::Uninterpreted("MyCustomType".into())
    );
    assert_eq!(
        canonical_sort("my::module::Foo"),
        CanonicalSort::Uninterpreted("Foo".into())
    );
    assert_eq!(
        canonical_sort("Option"),
        CanonicalSort::Uninterpreted("Option".into())
    );
}

#[test]
#[timeout(30000)]
fn test_model_predicates_match_only_bare_names() {
    assert!(is_seq_model_type("Vec"));
    assert!(is_fmap_model_type("HashMap"));
    assert!(is_mapping_model_type("Mapping"));
    assert!(is_int_model_type("HashSet"));

    assert!(
        !is_seq_model_type("std::vec::Vec"),
        "path stripping belongs to canonical_sort, not the raw Seq predicate"
    );
    assert!(
        !is_fmap_model_type("std::collections::HashMap"),
        "path stripping belongs to canonical_sort, not the raw FMap predicate"
    );
    assert!(
        !is_mapping_model_type("crate::logic::Mapping"),
        "path stripping belongs to canonical_sort, not the raw Mapping predicate"
    );
    assert!(
        !is_int_model_type("std::collections::HashSet"),
        "path stripping belongs to canonical_sort, not the raw Int-model predicate"
    );
}

#[test]
#[timeout(30000)]
fn test_int_model_predicate_includes_transparent_wrappers() {
    assert!(is_int_model_type("Rc"));
    assert!(is_int_model_type("Arc"));
    assert!(is_int_model_type("Box"));
    assert!(is_int_model_type("FSet"));
    assert!(is_int_model_type("GhostSet"));
}

#[test]
#[timeout(30000)]
fn test_canonical_sort_strips_paths_for_all_model_families() {
    assert_eq!(
        canonical_sort("std::collections::VecDeque"),
        CanonicalSort::Seq
    );
    assert_eq!(
        canonical_sort("std::collections::HashMap"),
        CanonicalSort::FMap
    );
    assert_eq!(
        canonical_sort("crate::logic::Mapping"),
        CanonicalSort::Mapping
    );
    assert_eq!(
        canonical_sort("std::collections::HashSet"),
        CanonicalSort::Int
    );
    assert_eq!(canonical_sort("alloc::rc::Rc"), CanonicalSort::Int);
    assert_eq!(canonical_sort("alloc::sync::Arc"), CanonicalSort::Int);
    assert_eq!(canonical_sort("alloc::boxed::Box"), CanonicalSort::Int);
}

#[test]
#[timeout(30000)]
fn test_canonical_sort_requires_exact_type_matches_after_stripping() {
    assert_eq!(
        canonical_sort("my::VecMap"),
        CanonicalSort::Uninterpreted("VecMap".into())
    );
    assert_eq!(
        canonical_sort("my::NotHashMap"),
        CanonicalSort::Uninterpreted("NotHashMap".into())
    );
    assert_eq!(
        canonical_sort("my::MappingView"),
        CanonicalSort::Uninterpreted("MappingView".into())
    );
    assert_eq!(
        canonical_sort("my::FSetWrapper"),
        CanonicalSort::Uninterpreted("FSetWrapper".into())
    );
}

#[test]
#[timeout(30000)]
fn test_expr_sort_to_ay_sort_respects_qualified_model_classification() {
    let cases = [
        ("std::collections::HashMap", fmap_sort()),
        ("crate::logic::Mapping", mapping_sort()),
        ("alloc::boxed::Box", Sort::Int),
    ];

    for (name, expected) in cases {
        let id = intern_sort_name(name);
        let actual = expr_sort_to_ay_sort(&ExprSort::Datatype(id));
        assert_eq!(
            actual, expected,
            "qualified datatype {name} should lower via canonical model classification"
        );
    }
}

/// Verify TypeParam encodes to Int (universal sort) for monomorphic
/// verification; an Uninterpreted sort would mismatch against the Int-sorted
/// values it is compared with. (#2551)
#[test]
#[timeout(30000)]
fn test_type_param_resolves_to_int() {
    let id = intern_sort_name("T");
    let expr_sort = ExprSort::TypeParam(id);
    let ay_sort = expr_sort_to_ay_sort(&expr_sort);
    assert_eq!(
        ay_sort,
        Sort::Int,
        "TypeParam should resolve to Int (universal sort)"
    );
}

/// Verify all type parameters resolve to Int (no distinct sorts needed in
/// monomorphic encoding). (#2551)
#[test]
#[timeout(30000)]
fn test_type_params_resolve_to_int() {
    let t_sort = expr_sort_to_ay_sort(&ExprSort::TypeParam(intern_sort_name("T")));
    let k_sort = expr_sort_to_ay_sort(&ExprSort::TypeParam(intern_sort_name("K")));
    assert_eq!(t_sort, Sort::Int, "TypeParam(T) should resolve to Int");
    assert_eq!(k_sort, Sort::Int, "TypeParam(K) should resolve to Int");
}

/// Verify TypeParam Display shows the parameter name. (#2062)
#[test]
#[timeout(30000)]
fn test_type_param_display() {
    let id = intern_sort_name("V");
    assert_eq!(ExprSort::TypeParam(id).to_string(), "TypeParam(V)");
}

/// Verify Ref(Datatype(Vec)) is recognized in canonical_sort pipeline.
#[test]
#[timeout(30000)]
fn test_ref_datatype_vec_canonical_sort_is_seq() {
    let id = intern_sort_name("std::vec::Vec");
    let ann = ExprSort::Ref(Box::new(ExprSort::Datatype(id)));
    let sort = expr_sort_to_ay_sort(&ann);
    assert_eq!(sort, Sort::seq(Sort::Int));
}

// ── ay_sort_to_expr_sort branch coverage ────────────────────────

/// Sort::Bool → ExprSort::Bool
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_bool() {
    assert_eq!(ay_sort_to_expr_sort(&Sort::Bool), Some(ExprSort::Bool));
}

/// Sort::Int → None (Int is the default, represented as None for backward compat)
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_int_is_none() {
    assert_eq!(ay_sort_to_expr_sort(&Sort::Int), None);
}

/// A float format's sort maps back to its float sort; `Real` is no float.
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_float_formats() {
    use trust_wp_core::formula::FloatWidth;
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::FloatingPoint(11, 53)),
        Some(ExprSort::Float(FloatWidth::F64))
    );
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::FloatingPoint(8, 24)),
        Some(ExprSort::Float(FloatWidth::F32))
    );
    assert_eq!(ay_sort_to_expr_sort(&Sort::FloatingPoint(5, 11)), None);
    assert_ne!(
        ay_sort_to_expr_sort(&Sort::Real),
        Some(ExprSort::Float(FloatWidth::F64))
    );
}

/// Sort::Seq(Int) → ExprSort::Seq (native sort path)
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_native_seq() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::seq(Sort::Int)),
        Some(ExprSort::Seq),
    );
}

/// Uninterpreted("Seq") is not special-cased: every Seq sort is native
/// Sort::Seq(Int), so the uninterpreted spelling falls through to
/// Datatype("Seq"). (#2080)
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_seq_uninterpreted_is_datatype_post_migration() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("Seq".to_string())),
        Some(ExprSort::Datatype(intern_sort_name("Seq"))),
    );
}

/// Uninterpreted("FMap") → ExprSort::FMap
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_fmap() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("FMap".to_string())),
        Some(ExprSort::FMap),
    );
}

/// Uninterpreted("Mapping") → ExprSort::Datatype("Mapping")
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_mapping() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("Mapping".to_string())),
        Some(ExprSort::Datatype(intern_sort_name("Mapping"))),
    );
}

/// Uninterpreted("Unit") → ExprSort::Unit
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_unit() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("Unit".to_string())),
        Some(ExprSort::Unit),
    );
}

/// Uninterpreted("Tuple2") → ExprSort::Tuple(2)
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_tuple() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("Tuple2".to_string())),
        Some(ExprSort::Tuple(2)),
    );
}

/// Uninterpreted("Tuple0") → ExprSort::Tuple(0)
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_tuple_zero() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("Tuple0".to_string())),
        Some(ExprSort::Tuple(0)),
    );
}

/// Uninterpreted("TupleXX") → None (non-numeric suffix, falls to Datatype)
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_tuple_invalid_suffix() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("TupleXX".to_string())),
        Some(ExprSort::Datatype(intern_sort_name("TupleXX"))),
    );
}

/// Uninterpreted("Option") → ExprSort::Datatype("Option")
#[test]
#[timeout(30000)]
fn test_ay_sort_to_expr_sort_generic_uninterpreted() {
    assert_eq!(
        ay_sort_to_expr_sort(&Sort::Uninterpreted("Option".to_string())),
        Some(ExprSort::Datatype(intern_sort_name("Option"))),
    );
}

/// Roundtrip: ExprSort → ay Sort → ExprSort for all stable sorts.
#[test]
#[timeout(30000)]
fn test_ay_sort_roundtrip_stable_sorts() {
    // Bool: ExprSort::Bool → Sort::Bool → ExprSort::Bool
    assert_eq!(
        ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::Bool)),
        Some(ExprSort::Bool),
    );
    // Seq: ExprSort::Seq → Sort::Seq(Int) → ExprSort::Seq
    assert_eq!(
        ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::Seq)),
        Some(ExprSort::Seq),
    );
    // FMap: ExprSort::FMap → Sort::Uninterpreted("FMap") → ExprSort::FMap
    assert_eq!(
        ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::FMap)),
        Some(ExprSort::FMap),
    );
    // Unit: ExprSort::Unit → Sort::Uninterpreted("Unit") → ExprSort::Unit
    assert_eq!(
        ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::Unit)),
        Some(ExprSort::Unit),
    );
    // Tuple: ExprSort::Tuple(3) → Sort::Uninterpreted("Tuple3") → ExprSort::Tuple(3)
    assert_eq!(
        ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::Tuple(3))),
        Some(ExprSort::Tuple(3)),
    );
    // Float: each format round-trips through its floating-point sort.
    for width in [
        trust_wp_core::formula::FloatWidth::F32,
        trust_wp_core::formula::FloatWidth::F64,
    ] {
        assert_eq!(
            ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::Float(width))),
            Some(ExprSort::Float(width)),
        );
    }
    // Int: ExprSort::Int → Sort::Int → None (Int is default, None is backward compat)
    assert_eq!(
        ay_sort_to_expr_sort(&expr_sort_to_ay_sort(&ExprSort::Int)),
        None,
    );
}

// ── MutRef sort encoding roundtrip (#2141) ──────────────────────

#[test]
#[timeout(30000)]
fn test_encode_name_component_roundtrip() {
    let original = "std::vec::Vec";
    let encoded = encode_name_component(original);
    let decoded = decode_name_component(&encoded);
    assert_eq!(decoded, Some(original.to_string()));
}

#[test]
#[timeout(30000)]
fn test_encode_name_component_simple() {
    let encoded = encode_name_component("T");
    assert_eq!(encoded, "54"); // 'T' = 0x54
}

#[test]
#[timeout(30000)]
fn test_decode_name_component_odd_length_returns_none() {
    assert_eq!(decode_name_component("abc"), None);
}

#[test]
#[timeout(30000)]
fn test_decode_name_component_invalid_hex_returns_none() {
    assert_eq!(decode_name_component("zz"), None);
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_inner_sort_primitives() {
    assert_eq!(encode_mutref_inner_sort(&ExprSort::Bool), "bool");
    assert_eq!(encode_mutref_inner_sort(&ExprSort::Int), "int");
    assert_eq!(encode_mutref_inner_sort(&ExprSort::Seq), "seq");
    assert_eq!(encode_mutref_inner_sort(&ExprSort::Unit), "unit");
    assert_eq!(encode_mutref_inner_sort(&ExprSort::FMap), "fmap");
    assert_eq!(
        encode_mutref_inner_sort(&ExprSort::Float(trust_wp_core::formula::FloatWidth::F64)),
        "float_f64"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_inner_sort_tuple() {
    assert_eq!(encode_mutref_inner_sort(&ExprSort::Tuple(3)), "tuple_3");
    assert_eq!(encode_mutref_inner_sort(&ExprSort::Tuple(0)), "tuple_0");
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_inner_sort_datatype() {
    let id = intern_sort_name("MyStruct");
    let encoded = encode_mutref_inner_sort(&ExprSort::Datatype(id));
    assert!(encoded.starts_with("datatype_"));
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_inner_sort_type_param() {
    let id = intern_sort_name("T");
    let encoded = encode_mutref_inner_sort(&ExprSort::TypeParam(id));
    assert!(encoded.starts_with("typeparam_"));
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_inner_sort_nested_ref() {
    let inner = ExprSort::Ref(Box::new(ExprSort::Int));
    let encoded = encode_mutref_inner_sort(&inner);
    assert_eq!(encoded, "ref_int");
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_inner_sort_nested_mutref() {
    let inner = ExprSort::MutRef(Box::new(ExprSort::Bool));
    let encoded = encode_mutref_inner_sort(&inner);
    assert_eq!(encoded, "mutref_bool");
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_inner_sort_primitives() {
    assert_eq!(decode_mutref_inner_sort("bool"), Some(ExprSort::Bool));
    assert_eq!(decode_mutref_inner_sort("int"), Some(ExprSort::Int));
    assert_eq!(decode_mutref_inner_sort("seq"), Some(ExprSort::Seq));
    assert_eq!(decode_mutref_inner_sort("unit"), Some(ExprSort::Unit));
    assert_eq!(decode_mutref_inner_sort("fmap"), Some(ExprSort::FMap));
    assert_eq!(
        decode_mutref_inner_sort("float_f32"),
        Some(ExprSort::Float(trust_wp_core::formula::FloatWidth::F32))
    );
    assert_eq!(decode_mutref_inner_sort("float"), None);
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_inner_sort_tuple() {
    assert_eq!(
        decode_mutref_inner_sort("tuple_3"),
        Some(ExprSort::Tuple(3))
    );
    assert_eq!(
        decode_mutref_inner_sort("tuple_0"),
        Some(ExprSort::Tuple(0))
    );
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_inner_sort_unknown_returns_none() {
    assert_eq!(decode_mutref_inner_sort("unknown_sort"), None);
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_inner_sort_nested_ref() {
    let decoded = decode_mutref_inner_sort("ref_int");
    assert_eq!(decoded, Some(ExprSort::Ref(Box::new(ExprSort::Int))));
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_inner_sort_nested_mutref() {
    let decoded = decode_mutref_inner_sort("mutref_bool");
    assert_eq!(decoded, Some(ExprSort::MutRef(Box::new(ExprSort::Bool))));
}

#[test]
#[timeout(30000)]
fn test_mutref_inner_sort_roundtrip_all_variants() {
    let variants: Vec<ExprSort> = vec![
        ExprSort::Bool,
        ExprSort::Int,
        ExprSort::Seq,
        ExprSort::Unit,
        ExprSort::FMap,
        ExprSort::Float(trust_wp_core::formula::FloatWidth::F32),
        ExprSort::Float(trust_wp_core::formula::FloatWidth::F64),
        ExprSort::Tuple(2),
        ExprSort::Datatype(intern_sort_name("Option")),
        ExprSort::TypeParam(intern_sort_name("K")),
        ExprSort::Ref(Box::new(ExprSort::Seq)),
        ExprSort::MutRef(Box::new(ExprSort::Int)),
    ];
    for sort in &variants {
        let encoded = encode_mutref_inner_sort(sort);
        let decoded = decode_mutref_inner_sort(&encoded);
        assert_eq!(
            decoded.as_ref(),
            Some(sort),
            "roundtrip failed for {sort:?} (encoded: {encoded:?})"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_encode_mutref_sort_name_has_prefix() {
    let name = encode_mutref_sort_name(&ExprSort::Int);
    assert!(name.starts_with("__trust_wp_mutref::"));
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_sort_name_roundtrip() {
    let inner = ExprSort::Seq;
    let name = encode_mutref_sort_name(&inner);
    let decoded = decode_mutref_sort_name(&name);
    assert_eq!(decoded, Some(ExprSort::MutRef(Box::new(ExprSort::Seq))));
}

#[test]
#[timeout(30000)]
fn test_decode_mutref_sort_name_non_prefix_returns_none() {
    assert_eq!(decode_mutref_sort_name("SomeOtherSort"), None);
}

#[test]
#[timeout(30000)]
fn test_mutref_expr_sort_to_ay_sort_roundtrip() {
    let sort = ExprSort::MutRef(Box::new(ExprSort::Int));
    let ay = expr_sort_to_ay_sort(&sort);
    let back = ay_sort_to_expr_sort(&ay);
    assert_eq!(
        back,
        Some(sort),
        "MutRef(Int) should roundtrip through ay sort"
    );
}

#[test]
#[timeout(30000)]
fn test_mutref_seq_roundtrip_through_ay() {
    let sort = ExprSort::MutRef(Box::new(ExprSort::Seq));
    let ay = expr_sort_to_ay_sort(&sort);
    let back = ay_sort_to_expr_sort(&ay);
    assert_eq!(back, Some(sort));
}

#[test]
#[timeout(30000)]
fn test_mutref_datatype_roundtrip_through_ay() {
    let id = intern_sort_name("MyStruct");
    let sort = ExprSort::MutRef(Box::new(ExprSort::Datatype(id)));
    let ay = expr_sort_to_ay_sort(&sort);
    let back = ay_sort_to_expr_sort(&ay);
    assert_eq!(back, Some(sort));
}

#[test]
#[timeout(30000)]
fn test_mutref_nested_ref_roundtrip_through_ay() {
    let sort = ExprSort::MutRef(Box::new(ExprSort::Ref(Box::new(ExprSort::Bool))));
    let ay = expr_sort_to_ay_sort(&sort);
    let back = ay_sort_to_expr_sort(&ay);
    assert_eq!(back, Some(sort));
}

#[test]
#[timeout(30000)]
fn test_mutref_type_param_roundtrip_through_ay() {
    let id = intern_sort_name("T");
    let sort = ExprSort::MutRef(Box::new(ExprSort::TypeParam(id)));
    let ay = expr_sort_to_ay_sort(&sort);
    let back = ay_sort_to_expr_sort(&ay);
    assert_eq!(back, Some(sort));
}

// --- #prophecy-slots (Fix B M1): instantiation-suffix grammar ---

#[test]
#[timeout(30000)]
fn mutref_instantiated_option_name_round_trips() {
    let payload = ExprSort::MutRef(Box::new(ExprSort::Int));
    let name = mutref_instantiated_option_name("std::option::Option", &payload);
    assert_eq!(name, "std::option::Option__twpm0_mutref_int");
    assert_eq!(parse_mutref_instantiated_option(&name), Some(payload));

    // core-pathed spelling parses identically.
    let payload = ExprSort::MutRef(Box::new(ExprSort::Bool));
    let name = mutref_instantiated_option_name("core::option::Option", &payload);
    assert_eq!(parse_mutref_instantiated_option(&name), Some(payload));

    // Nested referents survive the round trip.
    let payload = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int))));
    let name = mutref_instantiated_option_name("std::option::Option", &payload);
    assert_eq!(parse_mutref_instantiated_option(&name), Some(payload));
}

#[test]
#[timeout(30000)]
fn parse_mutref_instantiated_option_rejects_non_option_and_non_mutref() {
    // Non-Option base path: fail-closed None (stays an opaque sort).
    let payload = ExprSort::MutRef(Box::new(ExprSort::Int));
    let name = mutref_instantiated_option_name("m::MyEnum", &payload);
    assert_eq!(parse_mutref_instantiated_option(&name), None);

    // Undecodable token: None.
    assert_eq!(
        parse_mutref_instantiated_option("std::option::Option__twpm0_bogus"),
        None
    );

    // A non-MutRef payload token: None (the family lowering is scoped to
    // payloads that ARE mutable references at the top).
    assert_eq!(
        parse_mutref_instantiated_option("std::option::Option__twpm0_int"),
        None
    );

    // Plain names never parse.
    assert_eq!(
        parse_mutref_instantiated_option("std::option::Option"),
        None
    );
}

#[test]
#[timeout(30000)]
fn suffixed_option_annotation_maps_to_family_name_in_pure_lane() {
    let payload = ExprSort::MutRef(Box::new(ExprSort::Int));
    let name = mutref_instantiated_option_name("std::option::Option", &payload);
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(intern_sort_name(&name)));
    let payload_sort = expr_sort_to_ay_sort(&payload);
    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(payload_sort);
    assert_eq!(sort, Sort::Uninterpreted(family.name));
}

// --- #prophecy-slots (Fix B M2): carrier-tuple sort grammar ---

#[test]
#[timeout(30000)]
fn m2_carrier_tuple_sort_name_round_trips() {
    let elements = vec![
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        // `&mut [T]`: the driver cannot resolve the slice referent, so the
        // element is recorded as `legacy` rather than guessed at.
        None,
    ];
    let name = mutref_carrier_tuple_sort_name(&elements)
        .expect("a tuple with a &mut element mints a carrier sort");
    assert_eq!(name, "__trust_wp_mutref_tuple::mutref_int__legacy");
    assert_eq!(parse_mutref_carrier_tuple(&name), Some(elements));
}

#[test]
#[timeout(30000)]
fn m2_carrier_tuple_requires_at_least_one_mut_ref() {
    // No `&mut` element: no carrier sort, so the tuple keeps its plain
    // `Tuple{arity}` spelling and value-only tuples are untouched.
    assert_eq!(mutref_carrier_tuple_sort_name(&[None, None]), None);
    assert_eq!(mutref_carrier_tuple_sort_name(&[]), None);
    // A non-`MutRef` token is not a spelling this module mints — a
    // hand-written look-alike is refused whole.
    assert_eq!(
        parse_mutref_carrier_tuple("__trust_wp_mutref_tuple::int__legacy"),
        None
    );
    assert_eq!(
        parse_mutref_carrier_tuple("__trust_wp_mutref_tuple::legacy__legacy"),
        None
    );
    assert_eq!(
        parse_mutref_carrier_tuple("__trust_wp_mutref_tuple::"),
        None
    );
    assert_eq!(parse_mutref_carrier_tuple("Tuple2"), None);
}

#[test]
#[timeout(30000)]
fn m2_carrier_tuple_sort_keeps_its_full_name_not_the_bare_suffix() {
    // `canonical_sort` would `rsplit("::")` this name down to the element
    // list and conflate distinct instantiations. Both converter lanes must
    // return the FULL uninterpreted name.
    let name = mutref_carrier_tuple_sort_name(&[
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        Some(ExprSort::MutRef(Box::new(ExprSort::Bool))),
    ])
    .expect("carrier tuple");
    assert_eq!(name, "__trust_wp_mutref_tuple::mutref_int__mutref_bool");
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(intern_sort_name(&name)));
    assert_eq!(sort, Sort::Uninterpreted(name));
}

#[test]
#[timeout(30000)]
fn m2_option_of_carrier_tuple_parses_as_an_instantiated_option() {
    let tuple_name =
        mutref_carrier_tuple_sort_name(&[Some(ExprSort::MutRef(Box::new(ExprSort::Int))), None])
            .expect("carrier tuple");
    let payload = ExprSort::Datatype(intern_sort_name(&tuple_name));
    let name = mutref_instantiated_option_name("std::option::Option", &payload);
    assert_eq!(parse_mutref_instantiated_option(&name), Some(payload));

    // An `Option<SomeUserDatatype>` must NOT enter the carrier lane: the
    // payload datatype name has to parse as a carrier tuple.
    let plain = ExprSort::Datatype(intern_sort_name("m::MyStruct"));
    let plain_name = mutref_instantiated_option_name("std::option::Option", &plain);
    assert_eq!(parse_mutref_instantiated_option(&plain_name), None);
}

#[test]
#[timeout(30000)]
fn m2_option_of_carrier_tuple_maps_to_the_specialized_family() {
    let tuple_name =
        mutref_carrier_tuple_sort_name(&[Some(ExprSort::MutRef(Box::new(ExprSort::Int))), None])
            .expect("carrier tuple");
    let payload = ExprSort::Datatype(intern_sort_name(&tuple_name));
    let option_name = mutref_instantiated_option_name("std::option::Option", &payload);
    let sort = expr_sort_to_ay_sort(&ExprSort::Datatype(intern_sort_name(&option_name)));
    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(
        Sort::Uninterpreted(tuple_name),
    );
    assert_eq!(sort, Sort::Uninterpreted(family.name));
}

// --- the carrier recognizer (`ay_sort_contains_mut_ref_carrier`) ----------

#[test]
#[timeout(30000)]
fn carrier_recognizer_names_every_prophecy_carrier_spelling() {
    // the (current, final, id) record sort (#2141)
    let record = expr_sort_to_ay_sort(&ExprSort::MutRef(Box::new(ExprSort::Int)));
    assert!(ay_sort_contains_mut_ref_carrier(&record), "{record:?}");

    // the carrier TUPLE sort (Fix B M2)
    let tuple_name =
        mutref_carrier_tuple_sort_name(&[Some(ExprSort::MutRef(Box::new(ExprSort::Int))), None])
            .expect("carrier tuple");
    assert!(ay_sort_contains_mut_ref_carrier(&Sort::Uninterpreted(
        tuple_name.clone()
    )));

    // the instantiation-suffixed carrier Option (Fix B M1, blueprint C2)
    let option_name = mutref_instantiated_option_name(
        "std::option::Option",
        &ExprSort::MutRef(Box::new(ExprSort::Int)),
    );
    assert!(ay_sort_contains_mut_ref_carrier(&Sort::Uninterpreted(
        option_name
    )));
}

#[test]
#[timeout(30000)]
fn carrier_recognizer_leaves_value_sorts_alone() {
    for sort in [
        Sort::Int,
        Sort::Bool,
        Sort::Real,
        Sort::seq(Sort::Int),
        Sort::Uninterpreted("Mapping".to_string()),
        Sort::Uninterpreted("FMap".to_string()),
        Sort::Uninterpreted("Tuple2".to_string()),
        Sort::Uninterpreted("m::MyStruct".to_string()),
        expr_sort_to_ay_sort(&ExprSort::Ref(Box::new(ExprSort::Int))),
    ] {
        assert!(
            !ay_sort_contains_mut_ref_carrier(&sort),
            "value sort must not be refused: {sort:?}"
        );
    }
}

#[test]
#[timeout(30000)]
fn carrier_recognizer_sees_through_a_datatype_field_and_terminates_on_cycles() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let carrier = expr_sort_to_ay_sort(&ExprSort::MutRef(Box::new(ExprSort::Int)));
    let wrapper = Sort::Datatype(DatatypeSort::new(
        "m::Wrapper",
        vec![DatatypeConstructor::new(
            "m::Wrapper::New",
            vec![DatatypeField::new("f0", carrier)],
        )],
    ));
    assert!(ay_sort_contains_mut_ref_carrier(&wrapper));

    // A self-referential datatype must terminate and stay unrefused: the
    // back-edge carries no new evidence.
    let recursive_name = "m::Rec";
    let recursive = Sort::Datatype(DatatypeSort::new(
        recursive_name,
        vec![DatatypeConstructor::new(
            "m::Rec::Cons",
            vec![DatatypeField::new(
                "tail",
                Sort::Datatype(DatatypeSort::new(
                    recursive_name,
                    vec![DatatypeConstructor::new("m::Rec::Nil", vec![])],
                )),
            )],
        )],
    ));
    assert!(!ay_sort_contains_mut_ref_carrier(&recursive));
}

#[test]
#[timeout(30000)]
fn carrier_recognizer_resolves_the_uninterpreted_spelling_of_a_carrier_option() {
    // `stdlib_option_datatype_for_payload` hex-encodes the payload into the
    // FAMILY NAME, which is not the carrier grammar — so the `Uninterpreted`
    // spelling is only decidable through the declaration.
    let carrier = expr_sort_to_ay_sort(&ExprSort::MutRef(Box::new(ExprSort::Int)));
    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(carrier);
    let opaque = Sort::Uninterpreted(family.name.clone());

    assert!(
        !ay_sort_contains_mut_ref_carrier(&opaque),
        "the name alone cannot reveal the payload — this is the gap the \
         resolver closes, pinned so the resolver stays load-bearing"
    );
    assert!(
        ay_sort_contains_mut_ref_carrier_with(&opaque, &|name| (name == family.name)
            .then(|| family.clone())),
        "resolved through the declaration, the carrier payload must be seen"
    );
    // The `Datatype` spelling never needed the resolver.
    assert!(ay_sort_contains_mut_ref_carrier(&Sort::Datatype(family)));
}
