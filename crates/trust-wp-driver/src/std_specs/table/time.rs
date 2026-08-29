// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Duration and Instant specs.

use trust_wp_std::std::{duration, instant};

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // Duration specs
    (
        &["core::time::Duration::new", "std::time::Duration::new"],
        duration::specs::NEW,
    ),
    (
        &[
            "core::time::Duration::from_secs",
            "std::time::Duration::from_secs",
        ],
        duration::specs::FROM_SECS,
    ),
    (
        &[
            "core::time::Duration::from_millis",
            "std::time::Duration::from_millis",
        ],
        duration::specs::FROM_MILLIS,
    ),
    (
        &[
            "core::time::Duration::from_micros",
            "std::time::Duration::from_micros",
        ],
        duration::specs::FROM_MICROS,
    ),
    (
        &[
            "core::time::Duration::from_nanos",
            "std::time::Duration::from_nanos",
        ],
        duration::specs::FROM_NANOS,
    ),
    (
        &[
            "core::time::Duration::is_zero",
            "std::time::Duration::is_zero",
        ],
        duration::specs::IS_ZERO,
    ),
    (
        &[
            "core::time::Duration::as_secs",
            "std::time::Duration::as_secs",
        ],
        duration::specs::AS_SECS,
    ),
    (
        &[
            "core::time::Duration::as_millis",
            "std::time::Duration::as_millis",
        ],
        duration::specs::AS_MILLIS,
    ),
    (
        &[
            "core::time::Duration::as_micros",
            "std::time::Duration::as_micros",
        ],
        duration::specs::AS_MICROS,
    ),
    (
        &[
            "core::time::Duration::as_nanos",
            "std::time::Duration::as_nanos",
        ],
        duration::specs::AS_NANOS,
    ),
    (
        &[
            "core::time::Duration::subsec_millis",
            "std::time::Duration::subsec_millis",
        ],
        duration::specs::SUBSEC_MILLIS,
    ),
    (
        &[
            "core::time::Duration::subsec_micros",
            "std::time::Duration::subsec_micros",
        ],
        duration::specs::SUBSEC_MICROS,
    ),
    (
        &[
            "core::time::Duration::subsec_nanos",
            "std::time::Duration::subsec_nanos",
        ],
        duration::specs::SUBSEC_NANOS,
    ),
    (
        &[
            "core::time::Duration::checked_add",
            "std::time::Duration::checked_add",
        ],
        duration::specs::CHECKED_ADD,
    ),
    (
        &[
            "core::time::Duration::checked_sub",
            "std::time::Duration::checked_sub",
        ],
        duration::specs::CHECKED_SUB,
    ),
    (
        &[
            "core::time::Duration::checked_mul",
            "std::time::Duration::checked_mul",
        ],
        duration::specs::CHECKED_MUL,
    ),
    (
        &[
            "core::time::Duration::checked_div",
            "std::time::Duration::checked_div",
        ],
        duration::specs::CHECKED_DIV,
    ),
    // Duration Add/Sub use concrete impl paths only. The generic trait
    // paths (core::ops::Add::add, core::ops::Sub::sub) would match ANY
    // type implementing Add/Sub, not just Duration. The compiler resolves
    // Duration + Duration to <core::time::Duration as Add>::add, which
    // after normalization should match the concrete path. If the trait
    // fallback fires, it will produce core::ops::Add::add which we
    // intentionally do NOT match here to avoid conflicting with other impls.
    (
        &[
            "core::time::Duration::add",
            "std::time::Duration::add",
            "<core::time::Duration as core::ops::Add>::add",
            "<core::time::Duration as core::ops::arith::Add>::add",
            "<std::time::Duration as std::ops::Add>::add",
            "<core::time::Duration as std::ops::Add>::add",
            "<std::time::Duration as core::ops::Add>::add",
            "<std::time::Duration as core::ops::arith::Add>::add",
        ],
        duration::specs::ADD,
    ),
    (
        &[
            "core::time::Duration::sub",
            "std::time::Duration::sub",
            "<core::time::Duration as core::ops::Sub>::sub",
            "<core::time::Duration as core::ops::arith::Sub>::sub",
            "<std::time::Duration as std::ops::Sub>::sub",
            "<core::time::Duration as std::ops::Sub>::sub",
            "<std::time::Duration as core::ops::Sub>::sub",
            "<std::time::Duration as core::ops::arith::Sub>::sub",
        ],
        duration::specs::SUB,
    ),
    // Duration comparison operators — PartialEq and PartialOrd.
    // In MIR, `d1 == d2` becomes `<Duration as PartialEq>::eq`,
    // and `d1 >= d2` becomes `<Duration as PartialOrd>::ge`, etc.
    (
        &[
            "<core::time::Duration as core::cmp::PartialEq>::eq",
            "<std::time::Duration as core::cmp::PartialEq>::eq",
            "<core::time::Duration as std::cmp::PartialEq>::eq",
            "<std::time::Duration as std::cmp::PartialEq>::eq",
            "core::time::Duration::eq",
            "std::time::Duration::eq",
        ],
        duration::specs::PARTIAL_EQ,
    ),
    (
        &[
            "<core::time::Duration as core::cmp::PartialOrd>::ge",
            "<std::time::Duration as core::cmp::PartialOrd>::ge",
            "<core::time::Duration as std::cmp::PartialOrd>::ge",
            "<std::time::Duration as std::cmp::PartialOrd>::ge",
            "core::time::Duration::ge",
            "std::time::Duration::ge",
        ],
        duration::specs::GE,
    ),
    (
        &[
            "<core::time::Duration as core::cmp::PartialOrd>::gt",
            "<std::time::Duration as core::cmp::PartialOrd>::gt",
            "<core::time::Duration as std::cmp::PartialOrd>::gt",
            "<std::time::Duration as std::cmp::PartialOrd>::gt",
            "core::time::Duration::gt",
            "std::time::Duration::gt",
        ],
        duration::specs::GT,
    ),
    (
        &[
            "<core::time::Duration as core::cmp::PartialOrd>::le",
            "<std::time::Duration as core::cmp::PartialOrd>::le",
            "<core::time::Duration as std::cmp::PartialOrd>::le",
            "<std::time::Duration as std::cmp::PartialOrd>::le",
            "core::time::Duration::le",
            "std::time::Duration::le",
        ],
        duration::specs::LE,
    ),
    (
        &[
            "<core::time::Duration as core::cmp::PartialOrd>::lt",
            "<std::time::Duration as core::cmp::PartialOrd>::lt",
            "<core::time::Duration as std::cmp::PartialOrd>::lt",
            "<std::time::Duration as std::cmp::PartialOrd>::lt",
            "core::time::Duration::lt",
            "std::time::Duration::lt",
        ],
        duration::specs::LT,
    ),
    (
        &[
            "<core::time::Duration as core::cmp::PartialOrd>::partial_cmp",
            "<std::time::Duration as core::cmp::PartialOrd>::partial_cmp",
            "<core::time::Duration as std::cmp::PartialOrd>::partial_cmp",
            "<std::time::Duration as std::cmp::PartialOrd>::partial_cmp",
            "core::time::Duration::partial_cmp",
            "std::time::Duration::partial_cmp",
        ],
        duration::specs::PARTIAL_CMP,
    ),
    // Instant specs
    (
        &["std::time::Instant::now", "core::time::Instant::now"],
        instant::specs::NOW,
    ),
    (
        &[
            "std::time::Instant::elapsed",
            "core::time::Instant::elapsed",
        ],
        instant::specs::ELAPSED,
    ),
    (
        &[
            "std::time::Instant::checked_add",
            "core::time::Instant::checked_add",
        ],
        instant::specs::CHECKED_ADD,
    ),
    (
        &[
            "std::time::Instant::checked_sub",
            "core::time::Instant::checked_sub",
        ],
        instant::specs::CHECKED_SUB,
    ),
    (
        &[
            "std::time::Instant::duration_since",
            "core::time::Instant::duration_since",
        ],
        instant::specs::DURATION_SINCE,
    ),
    (
        &[
            "std::time::Instant::checked_duration_since",
            "core::time::Instant::checked_duration_since",
        ],
        instant::specs::CHECKED_DURATION_SINCE,
    ),
    (
        &[
            "std::time::Instant::saturating_duration_since",
            "core::time::Instant::saturating_duration_since",
        ],
        instant::specs::SATURATING_DURATION_SINCE,
    ),
    // Instant Add<Duration> operator.
    (
        &[
            "std::time::Instant::add",
            "core::time::Instant::add",
            "<std::time::Instant as core::ops::Add>::add",
            "<std::time::Instant as core::ops::arith::Add>::add",
            "<std::time::Instant as std::ops::Add>::add",
            "<core::time::Instant as core::ops::Add>::add",
            "<core::time::Instant as core::ops::arith::Add>::add",
            "<core::time::Instant as std::ops::Add>::add",
        ],
        instant::specs::ADD_DURATION,
    ),
    // Instant subtraction appears through both `Sub<Duration>` (returns
    // Instant) and `Sub<Instant>` (returns Duration). Since path lookup
    // cannot distinguish the two after generic normalization, use the
    // combined spec that is sound for both call shapes. (#967)
    (
        &[
            "std::time::Instant::sub",
            "core::time::Instant::sub",
            "<std::time::Instant as core::ops::Sub>::sub",
            "<std::time::Instant as core::ops::arith::Sub>::sub",
            "<std::time::Instant as std::ops::Sub>::sub",
            "<core::time::Instant as core::ops::Sub>::sub",
            "<core::time::Instant as core::ops::arith::Sub>::sub",
            "<core::time::Instant as std::ops::Sub>::sub",
        ],
        instant::specs::SUB_COMBINED,
    ),
    // Instant comparison operators — PartialEq and PartialOrd.
    (
        &[
            "<std::time::Instant as core::cmp::PartialOrd>::partial_cmp",
            "<core::time::Instant as core::cmp::PartialOrd>::partial_cmp",
            "<std::time::Instant as std::cmp::PartialOrd>::partial_cmp",
            "<core::time::Instant as std::cmp::PartialOrd>::partial_cmp",
            "std::time::Instant::partial_cmp",
            "core::time::Instant::partial_cmp",
        ],
        instant::specs::PARTIAL_CMP,
    ),
    (
        &[
            "<std::time::Instant as core::cmp::PartialEq>::eq",
            "<core::time::Instant as core::cmp::PartialEq>::eq",
            "<std::time::Instant as std::cmp::PartialEq>::eq",
            "<core::time::Instant as std::cmp::PartialEq>::eq",
            "std::time::Instant::eq",
            "core::time::Instant::eq",
        ],
        instant::specs::PARTIAL_EQ,
    ),
    (
        &[
            "<std::time::Instant as core::cmp::PartialOrd>::ge",
            "<core::time::Instant as core::cmp::PartialOrd>::ge",
            "<std::time::Instant as std::cmp::PartialOrd>::ge",
            "<core::time::Instant as std::cmp::PartialOrd>::ge",
            "std::time::Instant::ge",
            "core::time::Instant::ge",
        ],
        instant::specs::GE,
    ),
    (
        &[
            "<std::time::Instant as core::cmp::PartialOrd>::gt",
            "<core::time::Instant as core::cmp::PartialOrd>::gt",
            "<std::time::Instant as std::cmp::PartialOrd>::gt",
            "<core::time::Instant as std::cmp::PartialOrd>::gt",
            "std::time::Instant::gt",
            "core::time::Instant::gt",
        ],
        instant::specs::GT,
    ),
    (
        &[
            "<std::time::Instant as core::cmp::PartialOrd>::le",
            "<core::time::Instant as core::cmp::PartialOrd>::le",
            "<std::time::Instant as std::cmp::PartialOrd>::le",
            "<core::time::Instant as std::cmp::PartialOrd>::le",
            "std::time::Instant::le",
            "core::time::Instant::le",
        ],
        instant::specs::LE,
    ),
    (
        &[
            "<std::time::Instant as core::cmp::PartialOrd>::lt",
            "<core::time::Instant as core::cmp::PartialOrd>::lt",
            "<std::time::Instant as std::cmp::PartialOrd>::lt",
            "<core::time::Instant as std::cmp::PartialOrd>::lt",
            "std::time::Instant::lt",
            "core::time::Instant::lt",
        ],
        instant::specs::LT,
    ),
];
