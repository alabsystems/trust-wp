// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic Hash, Hasher, and BuildHasher trait specs.
//!
//! These are registered under bare trait method paths (e.g.,
//! `core::hash::Hash::hash`) so they match **any** `T: Hash` call
//! where no type-specific UFCS spec exists. Without these, Hash
//! trait calls fall through to opaque call handling, which assumes
//! `true` (unsound).
//!
//! The Hash trait is called implicitly during HashMap/HashSet operations
//! (insert, get, contains_key, etc.), so missing Hash specs cause
//! verification failures in any code that uses hash-based collections.

use trust_wp_std::std::hash;

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // ── Hash trait ─────────────────────────────────────────────────────
    (
        &["core::hash::Hash::hash", "std::hash::Hash::hash"],
        hash::specs::HASH,
    ),
    (
        &[
            "core::hash::Hash::hash_slice",
            "std::hash::Hash::hash_slice",
        ],
        hash::specs::HASH_SLICE,
    ),
    // ── Hasher trait ───────────────────────────────────────────────────
    (
        &["core::hash::Hasher::finish", "std::hash::Hasher::finish"],
        hash::specs::HASHER_FINISH,
    ),
    (
        &["core::hash::Hasher::write", "std::hash::Hasher::write"],
        hash::specs::HASHER_WRITE,
    ),
    (
        &[
            "core::hash::Hasher::write_u8",
            "std::hash::Hasher::write_u8",
        ],
        hash::specs::HASHER_WRITE_U8,
    ),
    (
        &[
            "core::hash::Hasher::write_u16",
            "std::hash::Hasher::write_u16",
        ],
        hash::specs::HASHER_WRITE_U16,
    ),
    (
        &[
            "core::hash::Hasher::write_u32",
            "std::hash::Hasher::write_u32",
        ],
        hash::specs::HASHER_WRITE_U32,
    ),
    (
        &[
            "core::hash::Hasher::write_u64",
            "std::hash::Hasher::write_u64",
        ],
        hash::specs::HASHER_WRITE_U64,
    ),
    (
        &[
            "core::hash::Hasher::write_usize",
            "std::hash::Hasher::write_usize",
        ],
        hash::specs::HASHER_WRITE_USIZE,
    ),
    (
        &[
            "core::hash::Hasher::write_i8",
            "std::hash::Hasher::write_i8",
        ],
        hash::specs::HASHER_WRITE_I8,
    ),
    (
        &[
            "core::hash::Hasher::write_i16",
            "std::hash::Hasher::write_i16",
        ],
        hash::specs::HASHER_WRITE_I16,
    ),
    (
        &[
            "core::hash::Hasher::write_i32",
            "std::hash::Hasher::write_i32",
        ],
        hash::specs::HASHER_WRITE_I32,
    ),
    (
        &[
            "core::hash::Hasher::write_i64",
            "std::hash::Hasher::write_i64",
        ],
        hash::specs::HASHER_WRITE_I64,
    ),
    (
        &[
            "core::hash::Hasher::write_isize",
            "std::hash::Hasher::write_isize",
        ],
        hash::specs::HASHER_WRITE_ISIZE,
    ),
    // ── BuildHasher trait ──────────────────────────────────────────────
    (
        &[
            "core::hash::BuildHasher::build_hasher",
            "std::hash::BuildHasher::build_hasher",
        ],
        hash::specs::BUILD_HASHER,
    ),
];
