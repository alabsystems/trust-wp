// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `discriminant.rs` datatype discriminant axiom encoding.
//!
//! Covers explicit discriminant values (#2631), index fallback, signed values,
//! and large unsigned discriminants.

use ay_dpll::api::{DatatypeSort, Sort};
use ntest::timeout;
use num_bigint::BigInt;

use super::super::AYEncoder;

/// When AdtDecl carries explicit discriminant values, the axioms must use
/// those values instead of the variant index. This prevents unsound encoding
/// for `#[repr]` enums with explicit `= N` assignments.
#[test]
#[timeout(30000)]
fn discriminant_axioms_use_explicit_values_not_indices() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtKind};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Simulate a #[repr(u8)] enum Status { Active = 10, Inactive = 20, Pending = 30 }
    let adt_decls = std::collections::HashMap::from([(
        "Status".to_string(),
        AdtDecl::new(
            "test::Status".to_string(),
            "Status".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new("Active".to_string(), "Active".to_string(), vec![])
                    .with_discriminant_value(10),
                AdtConstructorDecl::new("Inactive".to_string(), "Inactive".to_string(), vec![])
                    .with_discriminant_value(20),
                AdtConstructorDecl::new("Pending".to_string(), "Pending".to_string(), vec![])
                    .with_discriminant_value(30),
            ],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    // Create and declare the DatatypeSort
    let datatype = DatatypeSort {
        name: "Status".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Active".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Inactive".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Pending".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);

    // Get the discriminant function and constructor terms
    let sort_tag = AYEncoder::method_sort_tag(&Sort::Datatype(datatype.clone()));
    let smt_name = format!("method_discriminant_1_{sort_tag}");
    let discr_func = encoder.get_or_declare_method_func(
        &smt_name,
        &[Sort::Datatype(datatype.clone())],
        Sort::Int,
    );
    let active = encoder
        .solver
        .datatype_constructor(&datatype, "Active", &[]);
    let discr_active = encoder.solver.apply(&discr_func, &[active]);

    // The discriminant of Active should be 10, not 0
    let ten = encoder.solver.int_const(10);
    let eq_ten = encoder.solver.eq(discr_active, ten);
    let not_eq_ten = encoder.solver.not(eq_ten);
    encoder.solver.assert_term(not_eq_ten);

    // discriminant(Active) != 10 should be UNSAT (because axiom says == 10)
    let result = encoder.check_sat();
    assert!(
        matches!(result, crate::SolveResult::Unsat(_)),
        "discriminant(Active) should equal 10 for explicit discriminant, got {result:?}"
    );
}

/// Without AdtDecl (no discriminant metadata), axioms should fall back to
/// using variant indices (backward compatibility).
#[test]
#[timeout(30000)]
fn discriminant_axioms_fallback_to_index_without_adt_decl() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // No AdtDecl registered — encoder should fall back to enumerate() indices
    let datatype = DatatypeSort {
        name: "Color".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Red".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Green".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);

    let sort_tag = AYEncoder::method_sort_tag(&Sort::Datatype(datatype.clone()));
    let smt_name = format!("method_discriminant_1_{sort_tag}");
    let discr_func = encoder.get_or_declare_method_func(
        &smt_name,
        &[Sort::Datatype(datatype.clone())],
        Sort::Int,
    );
    let green = encoder.solver.datatype_constructor(&datatype, "Green", &[]);
    let discr_green = encoder.solver.apply(&discr_func, &[green]);

    // Green is index 1 — discriminant should be 1
    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(discr_green, one);
    let not_eq_one = encoder.solver.not(eq_one);
    encoder.solver.assert_term(not_eq_one);

    let result = encoder.check_sat();
    assert!(
        matches!(result, crate::SolveResult::Unsat(_)),
        "discriminant(Green) should equal 1 (variant index) without AdtDecl, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn discriminant_axioms_use_negative_signed_values() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtKind};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let adt_decls = std::collections::HashMap::from([(
        "SignedTag".to_string(),
        AdtDecl::new(
            "test::SignedTag".to_string(),
            "SignedTag".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new("Neg".to_string(), "Neg".to_string(), vec![])
                    .with_discriminant_value(-1),
                AdtConstructorDecl::new("Pos".to_string(), "Pos".to_string(), vec![])
                    .with_discriminant_value(2),
            ],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let datatype = DatatypeSort {
        name: "SignedTag".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Neg".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Pos".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);

    let sort_tag = AYEncoder::method_sort_tag(&Sort::Datatype(datatype.clone()));
    let smt_name = format!("method_discriminant_1_{sort_tag}");
    let discr_func = encoder.get_or_declare_method_func(
        &smt_name,
        &[Sort::Datatype(datatype.clone())],
        Sort::Int,
    );
    let neg = encoder.solver.datatype_constructor(&datatype, "Neg", &[]);
    let discr_neg = encoder.solver.apply(&discr_func, &[neg]);

    let minus_one = encoder.solver.int_const_bigint(&BigInt::from(-1));
    let eq_minus_one = encoder.solver.eq(discr_neg, minus_one);
    let not_eq_minus_one = encoder.solver.not(eq_minus_one);
    encoder.solver.assert_term(not_eq_minus_one);

    let result = encoder.check_sat();
    assert!(
        matches!(result, crate::SolveResult::Unsat(_)),
        "discriminant(Neg) should equal -1 for explicit signed discriminant, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn discriminant_axioms_preserve_large_unsigned_values() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtKind};

    let mut encoder = AYEncoder::new_with_quantifiers();
    let huge = BigInt::from(u128::MAX);

    let adt_decls = std::collections::HashMap::from([(
        "HugeTag".to_string(),
        AdtDecl::new(
            "test::HugeTag".to_string(),
            "HugeTag".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new("Huge".to_string(), "Huge".to_string(), vec![])
                    .with_discriminant_value(huge.clone()),
                AdtConstructorDecl::new("Small".to_string(), "Small".to_string(), vec![])
                    .with_discriminant_value(1),
            ],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let datatype = DatatypeSort {
        name: "HugeTag".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Huge".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Small".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);

    let sort_tag = AYEncoder::method_sort_tag(&Sort::Datatype(datatype.clone()));
    let smt_name = format!("method_discriminant_1_{sort_tag}");
    let discr_func = encoder.get_or_declare_method_func(
        &smt_name,
        &[Sort::Datatype(datatype.clone())],
        Sort::Int,
    );
    let huge_ctor = encoder.solver.datatype_constructor(&datatype, "Huge", &[]);
    let discr_huge = encoder.solver.apply(&discr_func, &[huge_ctor]);

    let huge_val = encoder.solver.int_const_bigint(&huge);
    let eq_huge = encoder.solver.eq(discr_huge, huge_val);
    let not_eq_huge = encoder.solver.not(eq_huge);
    encoder.solver.assert_term(not_eq_huge);

    let result = encoder.check_sat();
    assert!(
        matches!(result, crate::SolveResult::Unsat(_)),
        "discriminant(Huge) should preserve large explicit unsigned discriminants, got {result:?}"
    );
}
