// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Std-spec entries for `NonZero{U,I}{8,16,32,64,128,size}` types.
//!
//! NonZero types guarantee their inner value is not zero. The specs here
//! cover `new()`, `get()`, and `new_unchecked()` for all 12 NonZero types.
//!
//! MIR paths come in three forms:
//! - `core::num::NonZeroU32::new` (legacy named types)
//! - `core::num::NonZero::<u32>::new` (Rust 1.79+ generic form, normalized to `core::num::NonZero::new`)
//! - `std::num::NonZeroU32::new` (std re-export)
//!
//! Part of #2669

use trust_wp_std::std::num;

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // ── NonZero::new ───────────────────────────────────────────────
    //
    // All 12 NonZero types share the same spec for `new()`.
    // The generic `core::num::NonZero::new` path covers Rust 1.79+.
    (
        &[
            // Generic (Rust 1.79+): core::num::NonZero<T>::new normalizes to this
            "core::num::NonZero::new",
            "std::num::NonZero::new",
            // Legacy named types — unsigned
            "core::num::NonZeroU8::new",
            "std::num::NonZeroU8::new",
            "core::num::NonZeroU16::new",
            "std::num::NonZeroU16::new",
            "core::num::NonZeroU32::new",
            "std::num::NonZeroU32::new",
            "core::num::NonZeroU64::new",
            "std::num::NonZeroU64::new",
            "core::num::NonZeroU128::new",
            "std::num::NonZeroU128::new",
            "core::num::NonZeroUsize::new",
            "std::num::NonZeroUsize::new",
            // Legacy named types — signed
            "core::num::NonZeroI8::new",
            "std::num::NonZeroI8::new",
            "core::num::NonZeroI16::new",
            "std::num::NonZeroI16::new",
            "core::num::NonZeroI32::new",
            "std::num::NonZeroI32::new",
            "core::num::NonZeroI64::new",
            "std::num::NonZeroI64::new",
            "core::num::NonZeroI128::new",
            "std::num::NonZeroI128::new",
            "core::num::NonZeroIsize::new",
            "std::num::NonZeroIsize::new",
        ],
        num::specs::NONZERO_NEW,
    ),
    // ── NonZero::get ───────────────────────────────────────────────
    (
        &[
            // Generic (Rust 1.79+)
            "core::num::NonZero::get",
            "std::num::NonZero::get",
            // Legacy named types — unsigned
            "core::num::NonZeroU8::get",
            "std::num::NonZeroU8::get",
            "core::num::NonZeroU16::get",
            "std::num::NonZeroU16::get",
            "core::num::NonZeroU32::get",
            "std::num::NonZeroU32::get",
            "core::num::NonZeroU64::get",
            "std::num::NonZeroU64::get",
            "core::num::NonZeroU128::get",
            "std::num::NonZeroU128::get",
            "core::num::NonZeroUsize::get",
            "std::num::NonZeroUsize::get",
            // Legacy named types — signed
            "core::num::NonZeroI8::get",
            "std::num::NonZeroI8::get",
            "core::num::NonZeroI16::get",
            "std::num::NonZeroI16::get",
            "core::num::NonZeroI32::get",
            "std::num::NonZeroI32::get",
            "core::num::NonZeroI64::get",
            "std::num::NonZeroI64::get",
            "core::num::NonZeroI128::get",
            "std::num::NonZeroI128::get",
            "core::num::NonZeroIsize::get",
            "std::num::NonZeroIsize::get",
        ],
        num::specs::NONZERO_GET,
    ),
    // ── NonZero::new_unchecked ─────────────────────────────────────
    (
        &[
            // Generic (Rust 1.79+)
            "core::num::NonZero::new_unchecked",
            "std::num::NonZero::new_unchecked",
            // Legacy named types — unsigned
            "core::num::NonZeroU8::new_unchecked",
            "std::num::NonZeroU8::new_unchecked",
            "core::num::NonZeroU16::new_unchecked",
            "std::num::NonZeroU16::new_unchecked",
            "core::num::NonZeroU32::new_unchecked",
            "std::num::NonZeroU32::new_unchecked",
            "core::num::NonZeroU64::new_unchecked",
            "std::num::NonZeroU64::new_unchecked",
            "core::num::NonZeroU128::new_unchecked",
            "std::num::NonZeroU128::new_unchecked",
            "core::num::NonZeroUsize::new_unchecked",
            "std::num::NonZeroUsize::new_unchecked",
            // Legacy named types — signed
            "core::num::NonZeroI8::new_unchecked",
            "std::num::NonZeroI8::new_unchecked",
            "core::num::NonZeroI16::new_unchecked",
            "std::num::NonZeroI16::new_unchecked",
            "core::num::NonZeroI32::new_unchecked",
            "std::num::NonZeroI32::new_unchecked",
            "core::num::NonZeroI64::new_unchecked",
            "std::num::NonZeroI64::new_unchecked",
            "core::num::NonZeroI128::new_unchecked",
            "std::num::NonZeroI128::new_unchecked",
            "core::num::NonZeroIsize::new_unchecked",
            "std::num::NonZeroIsize::new_unchecked",
        ],
        num::specs::NONZERO_NEW_UNCHECKED,
    ),
];
