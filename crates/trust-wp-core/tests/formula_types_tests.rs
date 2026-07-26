// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::float_cmp, clippy::approx_constant)]

//! Unit tests for formula support types and helpers.
//!
//! Coverage gaps addressed:
//! - `float_bits.rs` (43 LOC): zero tests for FloatBits construction, round-trip, Display
//! - `types.rs` BinOp::smt_int_uf_name: zero direct unit tests
//! - `types.rs` Permission: new(), scaled_value(), constants — only incidental usage in SMT tests
//! - `types.rs` tuple/struct naming functions: heavily used but zero *correctness* unit tests
//! - `types.rs` named_struct_ctor_name / parse_named_struct_ctor: zero direct tests

use trust_wp_core::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
        tuple_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX,
        TUPLE_LOGIC_FN_PREFIX,
    },
    named_struct_ctor_name, parse_named_struct_ctor, BinOp, FloatBits, Permission,
};

// === FloatBits ===

#[test]
fn float_bits_from_f64_round_trip() {
    let vals = [0.0, 1.0, -1.0, 3.14, f64::MAX, f64::MIN, f64::MIN_POSITIVE];
    for v in vals {
        assert_eq!(
            FloatBits::from_f64(v).to_f64(),
            v,
            "round-trip failed for {v}"
        );
    }
}

#[test]
fn float_bits_from_f32_round_trip() {
    let vals: [f32; 4] = [0.0, 1.5, -2.25, f32::MAX];
    for v in vals {
        let bits = FloatBits::from_f32(v);
        let result = bits.to_f64();
        assert_eq!(result, f64::from(v), "f32 round-trip failed for {v}");
    }
}

#[test]
fn float_bits_nan_representable() {
    let nan = FloatBits::from_f64(f64::NAN);
    assert!(nan.to_f64().is_nan());
}

#[test]
fn float_bits_infinity_representable() {
    assert_eq!(FloatBits::from_f64(f64::INFINITY).to_f64(), f64::INFINITY);
    assert_eq!(
        FloatBits::from_f64(f64::NEG_INFINITY).to_f64(),
        f64::NEG_INFINITY
    );
}

#[test]
fn float_bits_equality() {
    assert_eq!(FloatBits::from_f64(1.0), FloatBits::from_f64(1.0));
    assert_ne!(FloatBits::from_f64(1.0), FloatBits::from_f64(2.0));
}

#[test]
fn float_bits_negative_zero_distinct() {
    // IEEE 754: +0.0 and -0.0 have different bit patterns
    let pos_zero = FloatBits::from_f64(0.0);
    let neg_zero = FloatBits::from_f64(-0.0);
    assert_ne!(pos_zero, neg_zero);
}

#[test]
fn float_bits_display() {
    assert_eq!(format!("{}", FloatBits::from_f64(3.14)), "3.14");
    assert_eq!(format!("{}", FloatBits::from_f64(0.0)), "0");
    assert_eq!(format!("{}", FloatBits::from_f64(-1.5)), "-1.5");
}

#[test]
fn float_bits_hash_consistent_with_eq() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(FloatBits::from_f64(1.0));
    set.insert(FloatBits::from_f64(1.0));
    assert_eq!(set.len(), 1);
    set.insert(FloatBits::from_f64(2.0));
    assert_eq!(set.len(), 2);
}

// === BinOp::smt_int_uf_name ===

#[test]
fn smt_uf_name_bitwise_ops() {
    assert_eq!(BinOp::Shl.smt_int_uf_name(), Some("__trust_wp_bit_shl"));
    assert_eq!(BinOp::Shr.smt_int_uf_name(), Some("__trust_wp_bit_shr"));
    assert_eq!(BinOp::BitAnd.smt_int_uf_name(), Some("__trust_wp_bit_and"));
    assert_eq!(BinOp::BitXor.smt_int_uf_name(), Some("__trust_wp_bit_xor"));
    assert_eq!(BinOp::BitOr.smt_int_uf_name(), Some("__trust_wp_bit_or"));
}

#[test]
fn smt_uf_name_none_for_arithmetic() {
    assert_eq!(BinOp::Add.smt_int_uf_name(), None);
    assert_eq!(BinOp::Sub.smt_int_uf_name(), None);
    assert_eq!(BinOp::Mul.smt_int_uf_name(), None);
    assert_eq!(BinOp::Div.smt_int_uf_name(), None);
    assert_eq!(BinOp::Mod.smt_int_uf_name(), None);
}

#[test]
fn smt_uf_name_none_for_comparison() {
    assert_eq!(BinOp::Eq.smt_int_uf_name(), None);
    assert_eq!(BinOp::Ne.smt_int_uf_name(), None);
    assert_eq!(BinOp::Lt.smt_int_uf_name(), None);
    assert_eq!(BinOp::Le.smt_int_uf_name(), None);
    assert_eq!(BinOp::Gt.smt_int_uf_name(), None);
    assert_eq!(BinOp::Ge.smt_int_uf_name(), None);
}

#[test]
fn smt_uf_name_none_for_logical() {
    assert_eq!(BinOp::And.smt_int_uf_name(), None);
    assert_eq!(BinOp::Or.smt_int_uf_name(), None);
    assert_eq!(BinOp::Implies.smt_int_uf_name(), None);
}

// === Permission ===

#[test]
fn permission_full_scaled_value() {
    assert_eq!(Permission::FULL.scaled_value(), Permission::PERM_SCALE);
}

#[test]
fn permission_half_scaled_value() {
    assert_eq!(Permission::HALF.scaled_value(), Permission::PERM_SCALE / 2);
}

#[test]
fn permission_new_valid() {
    let p = Permission::new(1, 4).expect("4 is non-zero");
    assert_eq!(p.numerator, 1);
    assert_eq!(p.denominator.get(), 4);
    assert_eq!(p.scaled_value(), Permission::PERM_SCALE / 4);
}

#[test]
fn permission_new_zero_denominator_returns_none() {
    assert!(Permission::new(1, 0).is_none());
}

#[test]
fn permission_new_zero_numerator() {
    let p = Permission::new(0, 1).expect("1 is non-zero");
    assert_eq!(p.scaled_value(), 0);
}

#[test]
fn permission_scaled_value_divides_evenly_up_to_10() {
    for denom in 1..=10_u32 {
        let p = Permission::new(1, denom).unwrap();
        let scaled = p.scaled_value();
        assert_eq!(
            scaled * i64::from(denom),
            Permission::PERM_SCALE,
            "1/{denom} * {denom} should equal PERM_SCALE"
        );
    }
}

// === tuple_logic_fn_name / arity ===

#[test]
fn tuple_logic_fn_name_format() {
    assert_eq!(tuple_logic_fn_name(0), "__trust_wp_tuple0");
    assert_eq!(tuple_logic_fn_name(2), "__trust_wp_tuple2");
    assert_eq!(tuple_logic_fn_name(10), "__trust_wp_tuple10");
}

#[test]
fn tuple_logic_fn_name_uses_prefix() {
    assert!(tuple_logic_fn_name(3).starts_with(TUPLE_LOGIC_FN_PREFIX));
}

#[test]
fn tuple_logic_fn_arity_round_trip() {
    for arity in 1..=10 {
        let name = tuple_logic_fn_name(arity);
        assert_eq!(
            tuple_logic_fn_arity(&name),
            Some(arity),
            "round-trip failed for arity {arity}"
        );
    }
}

#[test]
fn tuple_logic_fn_arity_zero_is_none() {
    // Arity 0 is explicitly rejected (unit type has no fields)
    assert_eq!(tuple_logic_fn_arity("__trust_wp_tuple0"), None);
}

#[test]
fn tuple_logic_fn_arity_non_tuple_name() {
    assert_eq!(tuple_logic_fn_arity("my_fn"), None);
    assert_eq!(tuple_logic_fn_arity(""), None);
    assert_eq!(tuple_logic_fn_arity("__trust_wp_tuple"), None);
}

#[test]
fn tuple_logic_fn_arity_invalid_suffix() {
    assert_eq!(tuple_logic_fn_arity("__trust_wp_tupleabc"), None);
    assert_eq!(tuple_logic_fn_arity("__trust_wp_tuple-1"), None);
}

// === tuple_field_logic_fn_name / index ===

#[test]
fn tuple_field_logic_fn_name_format() {
    assert_eq!(tuple_field_logic_fn_name(0), "__trust_wp_tuple_get_0");
    assert_eq!(tuple_field_logic_fn_name(1), "__trust_wp_tuple_get_1");
    assert_eq!(tuple_field_logic_fn_name(5), "__trust_wp_tuple_get_5");
}

#[test]
fn tuple_field_logic_fn_name_uses_prefix() {
    assert!(tuple_field_logic_fn_name(0).starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX));
}

#[test]
fn tuple_field_logic_fn_index_round_trip() {
    for idx in 0..10 {
        let name = tuple_field_logic_fn_name(idx);
        assert_eq!(
            tuple_field_logic_fn_index(&name),
            Some(idx),
            "round-trip failed for index {idx}"
        );
    }
}

#[test]
fn tuple_field_logic_fn_index_non_field_name() {
    assert_eq!(tuple_field_logic_fn_index("my_fn"), None);
    assert_eq!(tuple_field_logic_fn_index(""), None);
}

// === named_struct_ctor_name / parse_named_struct_ctor ===

#[test]
fn named_struct_ctor_name_single_field() {
    assert_eq!(
        named_struct_ctor_name("Point", &["x".to_string()]),
        "Point{x}"
    );
}

#[test]
fn named_struct_ctor_name_multiple_fields() {
    assert_eq!(
        named_struct_ctor_name("Point", &["x".to_string(), "y".to_string()]),
        "Point{x,y}"
    );
}

#[test]
fn named_struct_ctor_name_no_fields() {
    assert_eq!(named_struct_ctor_name("Unit", &[]), "Unit{}");
}

#[test]
fn parse_named_struct_ctor_round_trip() {
    let fields = vec!["x".to_string(), "y".to_string(), "z".to_string()];
    let name = named_struct_ctor_name("Vec3", &fields);
    let (type_name, parsed_fields) = parse_named_struct_ctor(&name).expect("should parse");
    assert_eq!(type_name, "Vec3");
    assert_eq!(parsed_fields, vec!["x", "y", "z"]);
}

#[test]
fn parse_named_struct_ctor_empty_fields() {
    let (type_name, fields) = parse_named_struct_ctor("Unit{}").expect("should parse");
    assert_eq!(type_name, "Unit");
    assert!(fields.is_empty());
}

#[test]
fn parse_named_struct_ctor_none_for_no_braces() {
    assert!(parse_named_struct_ctor("SomeType").is_none());
}

#[test]
fn parse_named_struct_ctor_none_for_unclosed_brace() {
    assert!(parse_named_struct_ctor("SomeType{x,y").is_none());
}

#[test]
fn parse_named_struct_ctor_qualified_type() {
    let name = named_struct_ctor_name("my_mod::MyStruct", &["val".to_string()]);
    let (type_name, fields) = parse_named_struct_ctor(&name).expect("should parse");
    assert_eq!(type_name, "my_mod::MyStruct");
    assert_eq!(fields, vec!["val"]);
}

// === NAMED_FIELD_LOGIC_FN_PREFIX ===

#[test]
fn named_field_prefix_value() {
    assert_eq!(NAMED_FIELD_LOGIC_FN_PREFIX, "__trust_wp_field_");
}
