// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! String, ops, sync, and bool specs.

use trust_wp_std::std::{ops, primitives, string, sync};

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    // String specs
    (
        &["alloc::string::String::new", "std::string::String::new"],
        string::specs::NEW,
    ),
    (
        &["alloc::string::String::len", "std::string::String::len"],
        string::specs::LEN,
    ),
    (
        &[
            "alloc::string::String::is_empty",
            "std::string::String::is_empty",
        ],
        string::specs::IS_EMPTY,
    ),
    (
        &[
            "alloc::string::String::push_str",
            "std::string::String::push_str",
        ],
        string::specs::PUSH_STR,
    ),
    (
        &["alloc::string::String::push", "std::string::String::push"],
        string::specs::PUSH,
    ),
    (
        &[
            "alloc::string::String::capacity",
            "std::string::String::capacity",
        ],
        string::specs::CAPACITY,
    ),
    (
        &["alloc::string::String::clear", "std::string::String::clear"],
        string::specs::CLEAR,
    ),
    // String::from(&str) — From<&str> for String
    (
        &[
            "<alloc::string::String as core::convert::From<&str>>::from",
            "<std::string::String as core::convert::From<&str>>::from",
            "<alloc::string::String as std::convert::From<&str>>::from",
            "<std::string::String as std::convert::From<&str>>::from",
            // Normalized forms (normalize_path strips `<&str>` as generic):
            "<alloc::string::String as core::convert::From>::from",
            "<std::string::String as core::convert::From>::from",
            "<alloc::string::String as std::convert::From>::from",
            "<std::string::String as std::convert::From>::from",
            "alloc::string::String::from",
            "std::string::String::from",
        ],
        string::specs::FROM_STR,
    ),
    // String::as_str
    (
        &[
            "alloc::string::String::as_str",
            "std::string::String::as_str",
        ],
        string::specs::AS_STR,
    ),
    // String additional methods
    (
        &[
            "alloc::string::String::truncate",
            "std::string::String::truncate",
        ],
        string::specs::TRUNCATE,
    ),
    (
        &[
            "alloc::string::String::contains",
            "std::string::String::contains",
        ],
        string::specs::CONTAINS,
    ),
    (
        &[
            "alloc::string::String::starts_with",
            "std::string::String::starts_with",
        ],
        string::specs::STARTS_WITH,
    ),
    (
        &[
            "alloc::string::String::ends_with",
            "std::string::String::ends_with",
        ],
        string::specs::ENDS_WITH,
    ),
    (
        &[
            "alloc::string::String::reserve",
            "std::string::String::reserve",
        ],
        string::specs::RESERVE,
    ),
    (
        &[
            "alloc::string::String::with_capacity",
            "std::string::String::with_capacity",
        ],
        string::specs::WITH_CAPACITY,
    ),
    (
        &[
            "alloc::string::String::insert",
            "std::string::String::insert",
        ],
        string::specs::INSERT,
    ),
    (
        &[
            "alloc::string::String::insert_str",
            "std::string::String::insert_str",
        ],
        string::specs::INSERT_STR,
    ),
    (
        &["alloc::string::String::pop", "std::string::String::pop"],
        string::specs::POP,
    ),
    (
        &[
            "alloc::string::String::remove",
            "std::string::String::remove",
        ],
        string::specs::REMOVE,
    ),
    (
        &[
            "alloc::string::String::retain",
            "std::string::String::retain",
        ],
        string::specs::RETAIN,
    ),
    // str specs
    (&["str::len", "core::str::len"], string::specs::STR_LEN),
    (
        &["str::is_empty", "core::str::is_empty"],
        string::specs::STR_IS_EMPTY,
    ),
    (
        &["str::contains", "core::str::contains"],
        string::specs::STR_CONTAINS,
    ),
    (
        &["str::starts_with", "core::str::starts_with"],
        string::specs::STR_STARTS_WITH,
    ),
    (
        &["str::ends_with", "core::str::ends_with"],
        string::specs::STR_ENDS_WITH,
    ),
    (&["str::trim", "core::str::trim"], string::specs::STR_TRIM),
    (
        &[
            "str::chars",
            "core::str::chars",
            // String deref paths — MIR may resolve String::chars through Deref to str::chars
            "alloc::string::String::chars",
            "std::string::String::chars",
        ],
        string::specs::STR_CHARS,
    ),
    (
        &[
            "str::bytes",
            "core::str::bytes",
            // String deref paths
            "alloc::string::String::bytes",
            "std::string::String::bytes",
        ],
        string::specs::STR_BYTES,
    ),
    (
        &[
            "str::split_at",
            "core::str::split_at",
            "alloc::string::String::split_at",
            "std::string::String::split_at",
        ],
        string::specs::STR_SPLIT_AT,
    ),
    // str::to_lowercase / str::to_uppercase — commonly used string transforms
    (
        &[
            "str::to_lowercase",
            "core::str::to_lowercase",
            "alloc::string::String::to_lowercase",
            "std::string::String::to_lowercase",
        ],
        string::specs::TO_LOWERCASE,
    ),
    (
        &[
            "str::to_uppercase",
            "core::str::to_uppercase",
            "alloc::string::String::to_uppercase",
            "std::string::String::to_uppercase",
        ],
        string::specs::TO_UPPERCASE,
    ),
    // ToString::to_string — covers both str and String
    (
        &[
            "<str as alloc::string::ToString>::to_string",
            "<str as std::string::ToString>::to_string",
            "str::to_string",
            "core::str::to_string",
            "<alloc::string::String as alloc::string::ToString>::to_string",
            "<std::string::String as std::string::ToString>::to_string",
            "alloc::string::ToString::to_string",
            "std::string::ToString::to_string",
        ],
        string::specs::TO_STRING,
    ),
    // Fn/FnMut/FnOnce closure call specs
    (
        &["core::ops::Fn::call", "std::ops::Fn::call"],
        ops::specs::FN_CALL,
    ),
    (
        &[
            "core::ops::Deref::deref",
            "core::ops::deref::Deref::deref",
            "std::ops::Deref::deref",
            "std::ops::deref::Deref::deref",
            // Arc UFCS Deref — MIR auto-deref can produce these (#2689)
            "<alloc::sync::Arc as core::ops::Deref>::deref",
            "<std::sync::Arc as core::ops::Deref>::deref",
            "<alloc::sync::Arc as core::ops::deref::Deref>::deref",
            "<std::sync::Arc as core::ops::deref::Deref>::deref",
            // Rc UFCS Deref
            "<alloc::rc::Rc as core::ops::Deref>::deref",
            "<std::rc::Rc as core::ops::Deref>::deref",
            "<alloc::rc::Rc as core::ops::deref::Deref>::deref",
            "<std::rc::Rc as core::ops::deref::Deref>::deref",
            // Vec UFCS Deref (Vec<T> -> &[T] coercion)
            "<alloc::vec::Vec as core::ops::Deref>::deref",
            "<std::vec::Vec as core::ops::Deref>::deref",
            "<alloc::vec::Vec as core::ops::deref::Deref>::deref",
            "<std::vec::Vec as core::ops::deref::Deref>::deref",
            // String UFCS Deref (String -> &str coercion)
            "<alloc::string::String as core::ops::Deref>::deref",
            "<std::string::String as core::ops::Deref>::deref",
            "<alloc::string::String as core::ops::deref::Deref>::deref",
            "<std::string::String as core::ops::deref::Deref>::deref",
        ],
        ops::specs::DEREF,
    ),
    (
        &[
            "core::ops::FnOnce::call_once",
            "std::ops::FnOnce::call_once",
        ],
        ops::specs::FN_ONCE_CALL_ONCE,
    ),
    (
        &[
            "core::ops::DerefMut::deref_mut",
            "core::ops::deref::DerefMut::deref_mut",
            "std::ops::DerefMut::deref_mut",
            "std::ops::deref::DerefMut::deref_mut",
            // Vec UFCS DerefMut — Vec<T> -> &mut [T] coercion (#2689)
            "<alloc::vec::Vec as core::ops::DerefMut>::deref_mut",
            "<std::vec::Vec as core::ops::DerefMut>::deref_mut",
            "<alloc::vec::Vec as core::ops::deref::DerefMut>::deref_mut",
            "<std::vec::Vec as core::ops::deref::DerefMut>::deref_mut",
        ],
        ops::specs::DEREF_MUT,
    ),
    (
        &["core::ops::FnMut::call_mut", "std::ops::FnMut::call_mut"],
        ops::specs::FN_MUT_CALL_MUT,
    ),
    // Mutex specs
    (
        &["std::sync::Mutex::new", "std::sync::mutex::Mutex::new"],
        sync::specs::MUTEX_NEW,
    ),
    (
        &["std::sync::Mutex::lock", "std::sync::mutex::Mutex::lock"],
        sync::specs::MUTEX_LOCK,
    ),
    (
        &[
            "std::sync::Mutex::into_inner",
            "std::sync::mutex::Mutex::into_inner",
        ],
        sync::specs::MUTEX_INTO_INNER,
    ),
    (
        &[
            "std::sync::Mutex::get_mut",
            "std::sync::mutex::Mutex::get_mut",
        ],
        sync::specs::MUTEX_GET_MUT,
    ),
    (
        &[
            "std::sync::MutexGuard::deref",
            "std::sync::mutex::MutexGuard::deref",
        ],
        sync::specs::MUTEX_GUARD_DEREF,
    ),
    (
        &[
            "std::sync::MutexGuard::set",
            "std::sync::mutex::MutexGuard::set",
        ],
        sync::specs::MUTEX_GUARD_SET,
    ),
    // Arc specs
    (
        &[
            "alloc::sync::Arc::new",
            "std::sync::Arc::new",
            "alloc::sync::new",
            "std::sync::new",
        ],
        sync::specs::ARC_NEW,
    ),
    (
        &[
            "alloc::sync::Arc::clone",
            "std::sync::Arc::clone",
            "<alloc::sync::Arc as core::clone::Clone>::clone",
            "<std::sync::Arc as core::clone::Clone>::clone",
            "<alloc::sync::Arc as std::clone::Clone>::clone",
            "<std::sync::Arc as std::clone::Clone>::clone",
            "alloc::sync::clone",
            "std::sync::clone",
        ],
        sync::specs::ARC_CLONE,
    ),
    (
        &[
            "alloc::sync::Arc::as_ref",
            "std::sync::Arc::as_ref",
            "<alloc::sync::Arc as core::convert::AsRef>::as_ref",
            "<std::sync::Arc as core::convert::AsRef>::as_ref",
            "<alloc::sync::Arc as std::convert::AsRef>::as_ref",
            "<std::sync::Arc as std::convert::AsRef>::as_ref",
            "alloc::sync::as_ref",
            "std::sync::as_ref",
        ],
        sync::specs::ARC_AS_REF,
    ),
    (
        &["alloc::sync::Arc::try_unwrap", "std::sync::Arc::try_unwrap"],
        sync::specs::ARC_TRY_UNWRAP,
    ),
    (
        &["alloc::sync::Arc::ptr_eq", "std::sync::Arc::ptr_eq"],
        sync::specs::ARC_PTR_EQ,
    ),
    // Rc specs
    (
        &[
            "alloc::rc::Rc::new",
            "std::rc::Rc::new",
            "alloc::rc::new",
            "std::rc::new",
        ],
        sync::specs::RC_NEW,
    ),
    (
        &[
            "alloc::rc::Rc::clone",
            "std::rc::Rc::clone",
            "<alloc::rc::Rc as core::clone::Clone>::clone",
            "<std::rc::Rc as core::clone::Clone>::clone",
            "<alloc::rc::Rc as std::clone::Clone>::clone",
            "<std::rc::Rc as std::clone::Clone>::clone",
            "alloc::rc::clone",
            "std::rc::clone",
        ],
        sync::specs::RC_CLONE,
    ),
    (
        &[
            "alloc::rc::Rc::as_ref",
            "std::rc::Rc::as_ref",
            "<alloc::rc::Rc as core::convert::AsRef>::as_ref",
            "<std::rc::Rc as core::convert::AsRef>::as_ref",
            "<alloc::rc::Rc as std::convert::AsRef>::as_ref",
            "<std::rc::Rc as std::convert::AsRef>::as_ref",
            "alloc::rc::as_ref",
            "std::rc::as_ref",
        ],
        sync::specs::RC_AS_REF,
    ),
    (
        &["alloc::rc::Rc::ptr_eq", "std::rc::Rc::ptr_eq"],
        sync::specs::RC_PTR_EQ,
    ),
    // Cell specs
    (
        &["core::cell::Cell::new", "std::cell::Cell::new"],
        sync::specs::CELL_NEW,
    ),
    (
        &["core::cell::Cell::get", "std::cell::Cell::get"],
        sync::specs::CELL_GET,
    ),
    (
        &["core::cell::Cell::set", "std::cell::Cell::set"],
        sync::specs::CELL_SET,
    ),
    // RefCell specs
    (
        &["core::cell::RefCell::new", "std::cell::RefCell::new"],
        sync::specs::REFCELL_NEW,
    ),
    (
        &["core::cell::RefCell::borrow", "std::cell::RefCell::borrow"],
        sync::specs::REFCELL_BORROW,
    ),
    (
        &[
            "core::cell::RefCell::borrow_mut",
            "std::cell::RefCell::borrow_mut",
        ],
        sync::specs::REFCELL_BORROW_MUT,
    ),
    // Thread spawn/join specs
    (
        &["std::thread::spawn", "std::thread::Builder::spawn"],
        sync::specs::SPAWN,
    ),
    (&["std::thread::JoinHandle::join"], sync::specs::JOIN),
    // Bool specs
    (
        &["core::bool::then", "bool::then"],
        primitives::specs::BOOL_THEN,
    ),
    (
        &["core::bool::then_some", "bool::then_some"],
        primitives::specs::BOOL_THEN_SOME,
    ),
    // str::to_owned / ToOwned::to_owned — creates owned String from &str
    (
        &[
            "<str as alloc::borrow::ToOwned>::to_owned",
            "<str as std::borrow::ToOwned>::to_owned",
            "str::to_owned",
            "core::str::to_owned",
            "<str as core::borrow::ToOwned>::to_owned",
        ],
        string::specs::TO_OWNED,
    ),
    // str utility methods — split, trim variants, replace, as_bytes, parse
    (
        &[
            "str::split",
            "core::str::split",
            "alloc::string::String::split",
            "std::string::String::split",
        ],
        string::specs::STR_SPLIT,
    ),
    (
        &[
            "str::split_whitespace",
            "core::str::split_whitespace",
            "alloc::string::String::split_whitespace",
            "std::string::String::split_whitespace",
        ],
        string::specs::STR_SPLIT_WHITESPACE,
    ),
    (
        &[
            "str::lines",
            "core::str::lines",
            "alloc::string::String::lines",
            "std::string::String::lines",
        ],
        string::specs::STR_LINES,
    ),
    (
        &["str::trim_start", "core::str::trim_start"],
        string::specs::STR_TRIM_START,
    ),
    (
        &["str::trim_end", "core::str::trim_end"],
        string::specs::STR_TRIM_END,
    ),
    (
        &[
            "str::replace",
            "core::str::replace",
            "alloc::string::String::replace",
            "std::string::String::replace",
        ],
        string::specs::STR_REPLACE,
    ),
    (
        &["str::as_bytes", "core::str::as_bytes"],
        string::specs::STR_AS_BYTES,
    ),
    (
        &["str::parse", "core::str::parse"],
        string::specs::STR_PARSE,
    ),
    // Generic From::from — trait fallback for From conversions
    // Type-specific From impls (e.g., String::from(&str)) match first
    // via earlier entries in string_sync or core_types tables.
    (
        &["core::convert::From::from", "std::convert::From::from"],
        ops::specs::FROM,
    ),
    // Generic Into::into — trait fallback for Into conversions
    (
        &["core::convert::Into::into", "std::convert::Into::into"],
        ops::specs::INTO,
    ),
    // Generic AsRef::as_ref — trait fallback for AsRef conversions
    // Type-specific specs (Arc::as_ref, Rc::as_ref) match first via
    // UFCS paths earlier in this table.
    (
        &[
            "core::convert::AsRef::as_ref",
            "std::convert::AsRef::as_ref",
        ],
        ops::specs::AS_REF_TRAIT,
    ),
    // Generic AsMut::as_mut — trait fallback for AsMut conversions
    (
        &[
            "core::convert::AsMut::as_mut",
            "std::convert::AsMut::as_mut",
        ],
        ops::specs::AS_MUT_TRAIT,
    ),
    // core::convert::identity — returns its argument unchanged
    (
        &["core::convert::identity", "std::convert::identity"],
        ops::specs::IDENTITY,
    ),
    // Generic TryFrom::try_from — trait fallback for fallible conversions
    (
        &[
            "core::convert::TryFrom::try_from",
            "std::convert::TryFrom::try_from",
        ],
        ops::specs::TRY_FROM,
    ),
    // Generic TryInto::try_into — trait fallback for fallible conversions
    (
        &[
            "core::convert::TryInto::try_into",
            "std::convert::TryInto::try_into",
        ],
        ops::specs::TRY_INTO,
    ),
    // str::find — returns first position of pattern match
    (
        &[
            "str::find",
            "core::str::find",
            "alloc::string::String::find",
            "std::string::String::find",
        ],
        string::specs::STR_FIND,
    ),
    // str::rfind — returns last position of pattern match
    (
        &[
            "str::rfind",
            "core::str::rfind",
            "alloc::string::String::rfind",
            "std::string::String::rfind",
        ],
        string::specs::STR_RFIND,
    ),
    // str::get — returns substring Option<&str>
    (&["str::get", "core::str::get"], string::specs::STR_GET),
    // str::splitn — splits at most n times
    (
        &[
            "str::splitn",
            "core::str::splitn",
            "alloc::string::String::splitn",
            "std::string::String::splitn",
        ],
        string::specs::STR_SPLITN,
    ),
    // str::rsplitn — splits from end at most n times
    (
        &[
            "str::rsplitn",
            "core::str::rsplitn",
            "alloc::string::String::rsplitn",
            "std::string::String::rsplitn",
        ],
        string::specs::STR_RSPLITN,
    ),
    // str::repeat — repeats string n times
    (
        &[
            "str::repeat",
            "core::str::repeat",
            "alloc::string::String::repeat",
            "std::string::String::repeat",
        ],
        string::specs::STR_REPEAT,
    ),
    // str::to_ascii_lowercase — returns ASCII lowercase string
    (
        &[
            "str::to_ascii_lowercase",
            "core::str::to_ascii_lowercase",
            "alloc::string::String::to_ascii_lowercase",
            "std::string::String::to_ascii_lowercase",
        ],
        string::specs::STR_TO_ASCII_LOWERCASE,
    ),
    // str::to_ascii_uppercase — returns ASCII uppercase string
    (
        &[
            "str::to_ascii_uppercase",
            "core::str::to_ascii_uppercase",
            "alloc::string::String::to_ascii_uppercase",
            "std::string::String::to_ascii_uppercase",
        ],
        string::specs::STR_TO_ASCII_UPPERCASE,
    ),
    // ── Arithmetic operator trait fallbacks ─────────────────────────
    // Generic specs for operator traits. Type-specific integer specs in
    // primitives_checked take first-match precedence. (#2689)
    (
        &[
            "core::ops::Add::add",
            "core::ops::arith::Add::add",
            "std::ops::Add::add",
        ],
        ops::specs::ADD,
    ),
    (
        &[
            "core::ops::Sub::sub",
            "core::ops::arith::Sub::sub",
            "std::ops::Sub::sub",
        ],
        ops::specs::SUB,
    ),
    (
        &[
            "core::ops::Mul::mul",
            "core::ops::arith::Mul::mul",
            "std::ops::Mul::mul",
        ],
        ops::specs::MUL,
    ),
    (
        &[
            "core::ops::Rem::rem",
            "core::ops::arith::Rem::rem",
            "std::ops::Rem::rem",
        ],
        ops::specs::REM,
    ),
    (
        &[
            "core::ops::Neg::neg",
            "core::ops::arith::Neg::neg",
            "std::ops::Neg::neg",
        ],
        ops::specs::NEG,
    ),
    // ── Bitwise operator trait fallbacks ──────────────────────────
    (
        &[
            "core::ops::BitAnd::bitand",
            "core::ops::bit::BitAnd::bitand",
            "std::ops::BitAnd::bitand",
        ],
        ops::specs::BIT_AND,
    ),
    (
        &[
            "core::ops::BitOr::bitor",
            "core::ops::bit::BitOr::bitor",
            "std::ops::BitOr::bitor",
        ],
        ops::specs::BIT_OR,
    ),
    (
        &[
            "core::ops::BitXor::bitxor",
            "core::ops::bit::BitXor::bitxor",
            "std::ops::BitXor::bitxor",
        ],
        ops::specs::BIT_XOR,
    ),
    (
        &[
            "core::ops::Not::not",
            "core::ops::bit::Not::not",
            "std::ops::Not::not",
        ],
        ops::specs::NOT,
    ),
    (
        &[
            "core::ops::Shl::shl",
            "core::ops::bit::Shl::shl",
            "std::ops::Shl::shl",
        ],
        ops::specs::SHL,
    ),
    (
        &[
            "core::ops::Shr::shr",
            "core::ops::bit::Shr::shr",
            "std::ops::Shr::shr",
        ],
        ops::specs::SHR,
    ),
    // ── Assignment operator trait fallbacks ───────────────────────
    (
        &[
            "core::ops::AddAssign::add_assign",
            "core::ops::arith::AddAssign::add_assign",
            "std::ops::AddAssign::add_assign",
        ],
        ops::specs::ADD_ASSIGN,
    ),
    (
        &[
            "core::ops::SubAssign::sub_assign",
            "core::ops::arith::SubAssign::sub_assign",
            "std::ops::SubAssign::sub_assign",
        ],
        ops::specs::SUB_ASSIGN,
    ),
    (
        &[
            "core::ops::MulAssign::mul_assign",
            "core::ops::arith::MulAssign::mul_assign",
            "std::ops::MulAssign::mul_assign",
        ],
        ops::specs::MUL_ASSIGN,
    ),
    (
        &[
            "core::ops::DivAssign::div_assign",
            "core::ops::arith::DivAssign::div_assign",
            "std::ops::DivAssign::div_assign",
        ],
        ops::specs::DIV_ASSIGN,
    ),
    (
        &[
            "core::ops::RemAssign::rem_assign",
            "core::ops::arith::RemAssign::rem_assign",
            "std::ops::RemAssign::rem_assign",
        ],
        ops::specs::REM_ASSIGN,
    ),
    // ── Borrow/Drop trait fallbacks ──────────────────────────────
    (
        &[
            "core::borrow::Borrow::borrow",
            "std::borrow::Borrow::borrow",
        ],
        ops::specs::BORROW,
    ),
    (
        &[
            "core::borrow::BorrowMut::borrow_mut",
            "std::borrow::BorrowMut::borrow_mut",
        ],
        ops::specs::BORROW_MUT,
    ),
    (
        &[
            "core::ops::Drop::drop",
            "core::ops::drop::Drop::drop",
            "std::ops::Drop::drop",
            "core::mem::drop",
            "std::mem::drop",
        ],
        ops::specs::DROP,
    ),
    // Generic Index::index trait fallback — MUST be after type-specific Index
    // specs (Vec, HashMap, slice) to preserve first-match precedence. (#2689)
    (
        &[
            "core::ops::Index::index",
            "core::ops::index::Index::index",
            "std::ops::Index::index",
            "std::ops::index::Index::index",
        ],
        ops::specs::INDEX,
    ),
    // Generic IndexMut::index_mut trait fallback — MUST be after type-specific
    // IndexMut specs (Vec, slice) to preserve first-match precedence. (#2689)
    (
        &[
            "core::ops::IndexMut::index_mut",
            "core::ops::index::IndexMut::index_mut",
            "std::ops::IndexMut::index_mut",
            "std::ops::index::IndexMut::index_mut",
        ],
        ops::specs::INDEX_MUT,
    ),
    // Generic Display::fmt trait fallback — prevents opaque classification
    // for any type implementing Display. (#2689)
    (
        &["core::fmt::Display::fmt", "std::fmt::Display::fmt"],
        ops::specs::DISPLAY_FMT,
    ),
    // Generic Debug::fmt trait fallback — prevents opaque classification
    // for any type implementing Debug. (#2689)
    (
        &["core::fmt::Debug::fmt", "std::fmt::Debug::fmt"],
        ops::specs::DEBUG_FMT,
    ),
    // ── Bitwise assignment operator trait fallbacks ──────────────
    // Completes the assignment-op coverage alongside AddAssign..RemAssign. (#2689)
    (
        &[
            "core::ops::BitAndAssign::bitand_assign",
            "core::ops::bit::BitAndAssign::bitand_assign",
            "std::ops::BitAndAssign::bitand_assign",
        ],
        ops::specs::BIT_AND_ASSIGN,
    ),
    (
        &[
            "core::ops::BitOrAssign::bitor_assign",
            "core::ops::bit::BitOrAssign::bitor_assign",
            "std::ops::BitOrAssign::bitor_assign",
        ],
        ops::specs::BIT_OR_ASSIGN,
    ),
    (
        &[
            "core::ops::BitXorAssign::bitxor_assign",
            "core::ops::bit::BitXorAssign::bitxor_assign",
            "std::ops::BitXorAssign::bitxor_assign",
        ],
        ops::specs::BIT_XOR_ASSIGN,
    ),
    (
        &[
            "core::ops::ShlAssign::shl_assign",
            "core::ops::bit::ShlAssign::shl_assign",
            "std::ops::ShlAssign::shl_assign",
        ],
        ops::specs::SHL_ASSIGN,
    ),
    (
        &[
            "core::ops::ShrAssign::shr_assign",
            "core::ops::bit::ShrAssign::shr_assign",
            "std::ops::ShrAssign::shr_assign",
        ],
        ops::specs::SHR_ASSIGN,
    ),
    // ── Formatting machinery ────────────────────────────────────
    // Internal formatting trait methods used by Display/Debug impls
    // and the write!/format! macros. Without these, any Display/Debug
    // impl that calls write_str triggers opaque fallback. (#2689)
    (
        &["core::fmt::Write::write_str", "std::fmt::Write::write_str"],
        ops::specs::FMT_WRITE_STR,
    ),
    (
        &["core::fmt::Write::write_fmt", "std::fmt::Write::write_fmt"],
        ops::specs::FMT_WRITE_FMT,
    ),
    (
        &[
            "core::fmt::Formatter::write_str",
            "std::fmt::Formatter::write_str",
        ],
        ops::specs::FORMATTER_WRITE_STR,
    ),
    (
        &[
            "core::fmt::Formatter::write_fmt",
            "std::fmt::Formatter::write_fmt",
        ],
        ops::specs::FORMATTER_WRITE_FMT,
    ),
    // Generic IntoIterator::into_iter trait fallback — MUST be after
    // type-specific into_iter specs (Vec, HashMap, Range, etc.) to
    // preserve first-match precedence. (#2689)
    (
        &[
            "core::iter::IntoIterator::into_iter",
            "core::iter::traits::collect::IntoIterator::into_iter",
            "std::iter::IntoIterator::into_iter",
        ],
        ops::specs::INTO_ITER,
    ),
    // Generic Extend::extend trait fallback — MUST be after
    // type-specific extend specs (Vec, HashMap, HashSet). (#2689)
    (
        &[
            "core::iter::Extend::extend",
            "core::iter::traits::collect::Extend::extend",
            "std::iter::Extend::extend",
        ],
        ops::specs::EXTEND,
    ),
    // core::ptr::drop_in_place — called by drop glue, prevents
    // opaque classification for destructor calls. (#2689)
    (
        &["core::ptr::drop_in_place", "std::ptr::drop_in_place"],
        ops::specs::DROP_IN_PLACE,
    ),
    // =========================================================================
    // Atomic operation specs — trust-wp-std wrapper types (#2697)
    // =========================================================================
    // These prevent OpaqueCallTrueAssumption for Creusot's atomic wrappers.
    // Both SC and RelAcq variants are covered. MIR paths resolve through
    // trust_wp_std (or creusot_std → trust_wp_std).
    //
    // AtomicBool
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicBool::new",
            "trust_wp_std::std::sync::atomic_relacq::AtomicBool::new",
        ],
        sync::specs::ATOMIC_NEW,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicBool::into_inner",
            "trust_wp_std::std::sync::atomic_relacq::AtomicBool::into_inner",
        ],
        sync::specs::ATOMIC_INTO_INNER,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicBool::load",
            "trust_wp_std::std::sync::atomic_relacq::AtomicBool::load",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicBool::store",
            "trust_wp_std::std::sync::atomic_relacq::AtomicBool::store",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicBool::swap",
            "trust_wp_std::std::sync::atomic_relacq::AtomicBool::swap",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
    // AtomicUsize
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicUsize::new",
            "trust_wp_std::std::sync::atomic_relacq::AtomicUsize::new",
        ],
        sync::specs::ATOMIC_NEW,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicUsize::into_inner",
            "trust_wp_std::std::sync::atomic_relacq::AtomicUsize::into_inner",
        ],
        sync::specs::ATOMIC_INTO_INNER,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicUsize::load",
            "trust_wp_std::std::sync::atomic_relacq::AtomicUsize::load",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicUsize::store",
            "trust_wp_std::std::sync::atomic_relacq::AtomicUsize::store",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicUsize::swap",
            "trust_wp_std::std::sync::atomic_relacq::AtomicUsize::swap",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicUsize::fetch_add",
            "trust_wp_std::std::sync::atomic_relacq::AtomicUsize::fetch_add",
        ],
        sync::specs::ATOMIC_FETCH_ADD,
    ),
    // AtomicI32
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicI32::new",
            "trust_wp_std::std::sync::atomic_relacq::AtomicI32::new",
        ],
        sync::specs::ATOMIC_NEW,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicI32::into_inner",
            "trust_wp_std::std::sync::atomic_relacq::AtomicI32::into_inner",
        ],
        sync::specs::ATOMIC_INTO_INNER,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicI32::load",
            "trust_wp_std::std::sync::atomic_relacq::AtomicI32::load",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicI32::store",
            "trust_wp_std::std::sync::atomic_relacq::AtomicI32::store",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicI32::swap",
            "trust_wp_std::std::sync::atomic_relacq::AtomicI32::swap",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicI32::fetch_add",
            "trust_wp_std::std::sync::atomic_relacq::AtomicI32::fetch_add",
        ],
        sync::specs::ATOMIC_FETCH_ADD,
    ),
    // AtomicU32
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU32::new",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU32::new",
        ],
        sync::specs::ATOMIC_NEW,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU32::into_inner",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU32::into_inner",
        ],
        sync::specs::ATOMIC_INTO_INNER,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU32::load",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU32::load",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU32::store",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU32::store",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU32::swap",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU32::swap",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU32::fetch_add",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU32::fetch_add",
        ],
        sync::specs::ATOMIC_FETCH_ADD,
    ),
    // AtomicU64
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU64::new",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU64::new",
        ],
        sync::specs::ATOMIC_NEW,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU64::into_inner",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU64::into_inner",
        ],
        sync::specs::ATOMIC_INTO_INNER,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU64::load",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU64::load",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU64::store",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU64::store",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU64::swap",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU64::swap",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::AtomicU64::fetch_add",
            "trust_wp_std::std::sync::atomic_relacq::AtomicU64::fetch_add",
        ],
        sync::specs::ATOMIC_FETCH_ADD,
    ),
    // =========================================================================
    // Atomic committer ghost method specs (#2697)
    // =========================================================================
    // Committer methods (val, ward, shoot, shot, old_val, new_val) are ghost-only.
    // Empty specs prevent opaque classification.
    //
    // SC committers
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::LoadCommitter::val",
            "trust_wp_std::std::sync::atomic_sc::LoadCommitter::ward",
            "trust_wp_std::std::sync::atomic_sc::LoadCommitter::shoot",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::StoreCommitter::val",
            "trust_wp_std::std::sync::atomic_sc::StoreCommitter::ward",
            "trust_wp_std::std::sync::atomic_sc::StoreCommitter::shot",
            "trust_wp_std::std::sync::atomic_sc::StoreCommitter::shoot",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_sc::UpdateCommitter::shot",
            "trust_wp_std::std::sync::atomic_sc::UpdateCommitter::ward",
            "trust_wp_std::std::sync::atomic_sc::UpdateCommitter::old_val",
            "trust_wp_std::std::sync::atomic_sc::UpdateCommitter::new_val",
            "trust_wp_std::std::sync::atomic_sc::UpdateCommitter::shoot",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
    // RelAcq committers
    (
        &[
            "trust_wp_std::std::sync::atomic_relacq::LoadCommitter::val",
            "trust_wp_std::std::sync::atomic_relacq::LoadCommitter::ward",
            "trust_wp_std::std::sync::atomic_relacq::LoadCommitter::shoot",
        ],
        sync::specs::ATOMIC_LOAD,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_relacq::StoreCommitter::val",
            "trust_wp_std::std::sync::atomic_relacq::StoreCommitter::ward",
            "trust_wp_std::std::sync::atomic_relacq::StoreCommitter::shot",
            "trust_wp_std::std::sync::atomic_relacq::StoreCommitter::shoot",
        ],
        sync::specs::ATOMIC_STORE,
    ),
    (
        &[
            "trust_wp_std::std::sync::atomic_relacq::UpdateCommitter::shot",
            "trust_wp_std::std::sync::atomic_relacq::UpdateCommitter::ward",
            "trust_wp_std::std::sync::atomic_relacq::UpdateCommitter::old_val",
            "trust_wp_std::std::sync::atomic_relacq::UpdateCommitter::new_val",
            "trust_wp_std::std::sync::atomic_relacq::UpdateCommitter::shoot",
        ],
        sync::specs::ATOMIC_SWAP,
    ),
];
