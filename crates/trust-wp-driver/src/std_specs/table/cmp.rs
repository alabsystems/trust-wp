// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic comparison trait specs (PartialEq, PartialOrd, Ord).
//!
//! These are registered under bare trait method paths (e.g.,
//! `core::cmp::PartialOrd::le`) so they match **any** `T: PartialOrd`
//! call where no type-specific UFCS spec exists. Type-specific specs
//! (like Duration's `<Duration as PartialOrd>::le`) take precedence
//! because UFCS lookup (Step 3) runs before trait fallback (Step 5)
//! in `call_spec.rs`.
//!
//! Pattern follows `core::ops::Fn::call` in string_sync.rs.

use trust_wp_std::std::cmp;

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // PartialEq trait methods
    (
        &[
            "core::cmp::PartialEq::eq",
            "std::cmp::PartialEq::eq",
            "core::cmp::PartialEq<Self>::eq",
        ],
        cmp::specs::PARTIAL_EQ,
    ),
    (
        &[
            "core::cmp::PartialEq::ne",
            "std::cmp::PartialEq::ne",
            "core::cmp::PartialEq<Self>::ne",
        ],
        cmp::specs::NE,
    ),
    // PartialOrd trait methods
    (
        &[
            "core::cmp::PartialOrd::partial_cmp",
            "std::cmp::PartialOrd::partial_cmp",
            "core::cmp::PartialOrd<Self>::partial_cmp",
        ],
        cmp::specs::PARTIAL_CMP,
    ),
    (
        &[
            "core::cmp::PartialOrd::le",
            "std::cmp::PartialOrd::le",
            "core::cmp::PartialOrd<Self>::le",
        ],
        cmp::specs::LE,
    ),
    (
        &[
            "core::cmp::PartialOrd::ge",
            "std::cmp::PartialOrd::ge",
            "core::cmp::PartialOrd<Self>::ge",
        ],
        cmp::specs::GE,
    ),
    (
        &[
            "core::cmp::PartialOrd::lt",
            "std::cmp::PartialOrd::lt",
            "core::cmp::PartialOrd<Self>::lt",
        ],
        cmp::specs::LT,
    ),
    (
        &[
            "core::cmp::PartialOrd::gt",
            "std::cmp::PartialOrd::gt",
            "core::cmp::PartialOrd<Self>::gt",
        ],
        cmp::specs::GT,
    ),
    // Ord trait methods
    (
        &["core::cmp::Ord::cmp", "std::cmp::Ord::cmp"],
        cmp::specs::CMP,
    ),
    (
        &["core::cmp::Ord::max", "std::cmp::Ord::max"],
        cmp::specs::MAX,
    ),
    (
        &["core::cmp::Ord::min", "std::cmp::Ord::min"],
        cmp::specs::MIN,
    ),
    (
        &["core::cmp::Ord::clamp", "std::cmp::Ord::clamp"],
        cmp::specs::CLAMP,
    ),
    // Ordering methods
    (
        &["core::cmp::Ordering::then", "std::cmp::Ordering::then"],
        cmp::specs::ORDERING_THEN,
    ),
    (
        &[
            "core::cmp::Ordering::then_with",
            "std::cmp::Ordering::then_with",
        ],
        cmp::specs::ORDERING_THEN_WITH,
    ),
    (
        &[
            "core::cmp::Ordering::reverse",
            "std::cmp::Ordering::reverse",
        ],
        cmp::specs::ORDERING_REVERSE,
    ),
    (
        &["core::cmp::Ordering::is_eq", "std::cmp::Ordering::is_eq"],
        cmp::specs::ORDERING_IS_EQ,
    ),
    (
        &["core::cmp::Ordering::is_lt", "std::cmp::Ordering::is_lt"],
        cmp::specs::ORDERING_IS_LT,
    ),
    (
        &["core::cmp::Ordering::is_gt", "std::cmp::Ordering::is_gt"],
        cmp::specs::ORDERING_IS_GT,
    ),
    (
        &["core::cmp::Ordering::is_le", "std::cmp::Ordering::is_le"],
        cmp::specs::ORDERING_IS_LE,
    ),
    (
        &["core::cmp::Ordering::is_ge", "std::cmp::Ordering::is_ge"],
        cmp::specs::ORDERING_IS_GE,
    ),
    // Free functions: cmp::min, cmp::max, cmp::min_by_key, cmp::max_by_key
    (&["core::cmp::min", "std::cmp::min"], cmp::specs::CMP_MIN),
    (&["core::cmp::max", "std::cmp::max"], cmp::specs::CMP_MAX),
    (
        &["core::cmp::min_by_key", "std::cmp::min_by_key"],
        cmp::specs::CMP_MIN_BY_KEY,
    ),
    (
        &["core::cmp::max_by_key", "std::cmp::max_by_key"],
        cmp::specs::CMP_MAX_BY_KEY,
    ),
];
