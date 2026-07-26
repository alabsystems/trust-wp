// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Built-in extern-spec registry for trust-wp-std.
//!
//! This module exposes the extern-spec declarations from `extern_specs.rs`
//! as a static, queryable registry that the driver can import directly —
//! without walking `tcx.iter_local_def_id()` (which only sees local crate
//! definitions).
//!
//! The driver merges this registry into its `extern_specs` map before local
//! discovery, so user-defined `extern_spec!` declarations override these
//! built-in entries.
//!
//! See: `designs/2026-03-12-1672-extern-spec-registry-bridge.md`

/// A built-in extern-spec entry from trust-wp-std.
///
/// Uses the same spec-string format as `StdSpec::from_spec_string()`:
/// ```text
/// params: self, index, element
/// requires: index@ <= self@.len()
/// ensures: (^self)@.len() == self@.len() + 1
/// ```
#[derive(Debug, Clone)]
pub struct BuiltinExternSpec {
    /// Normalized target function path (e.g., `"std::vec::Vec::new"`).
    pub target_path: &'static str,
    /// Spec in spec-string format, parseable by `StdSpec::from_spec_string()`.
    pub spec: &'static str,
}

/// All built-in extern-spec entries from trust-wp-std.
///
/// This mirrors the `extern_spec!` declarations in `extern_specs.rs` as
/// static data. Entries without any requires/ensures clauses are omitted.
pub static BUILTIN_EXTERN_SPECS: &[BuiltinExternSpec] = &[
    // ── Vec<T> inherent methods ─────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::vec::Vec::new",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::with_capacity",
        spec: "\
            params: capacity\n\
            ensures: result@.len() == 0\n\
            ensures: result.capacity()@ >= capacity@",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::len",
        spec: "ensures: result@ == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::is_empty",
        spec: "ensures: result == (self@.len() == 0)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::push",
        spec: "\
            params: self, value\n\
            ensures: (^self)@ == self@.push_back(value)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::clear",
        spec: "ensures: (^self)@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::capacity",
        spec: "ensures: result@ >= self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::insert",
        spec: "\
            params: self, index, element\n\
            requires: index@ <= self@.len()\n\
            ensures: (^self)@.len() == self@.len() + 1\n\
            ensures: (^self)@.index_logic(index@) == element",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::remove",
        spec: "\
            params: self, index\n\
            requires: index@ < self@.len()\n\
            ensures: result == self@.index_logic(index@)\n\
            ensures: (^self)@.len() == self@.len() - 1",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::get",
        spec: "\
            params: self, ix\n\
            ensures: ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)\n\
            ensures: !ix.in_bounds(self@) ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::get_mut",
        spec: "\
            params: self, ix\n\
            ensures: ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, r)\n\
            ensures: ix.in_bounds(self@) ==> ix.has_value((^self)@, ^result)\n\
            ensures: ix.in_bounds(self@) ==> ix.resolve_elsewhere(self@, (^self)@)\n\
            ensures: ix.in_bounds(self@) ==> (^self)@.len() == self@.len()\n\
            ensures: !ix.in_bounds(self@) ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::reserve",
        spec: "\
            params: self, additional\n\
            ensures: (^self)@ == self@\n\
            ensures: (^self)@.len() == self@.len()\n\
            ensures: forall<i: Int> 0 <= i && i < self@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::reserve_exact",
        spec: "\
            params: self, additional\n\
            ensures: (^self)@ == self@\n\
            ensures: (^self)@.len() == self@.len()\n\
            ensures: forall<i: Int> 0 <= i && i < self@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::shrink_to_fit",
        spec: "\
            ensures: (^self)@ == self@\n\
            ensures: (^self)@.len() == self@.len()\n\
            ensures: forall<i: Int> 0 <= i && i < self@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::shrink_to",
        spec: "\
            params: self, min_capacity\n\
            ensures: (^self)@ == self@\n\
            ensures: (^self)@.len() == self@.len()\n\
            ensures: forall<i: Int> 0 <= i && i < self@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::extend_from_slice",
        spec: "\
            params: self, other\n\
            ensures: (^self)@.len() == self@.len() + other@.len()\n\
            ensures: forall<i: Int> 0 <= i && i < self@.len() ==> (^self)@.index_logic(i) == self@.index_logic(i)\n\
            ensures: forall<i: Int> 0 <= i && i < other@.len() ==> (^self)@.index_logic(self@.len() + i) == other@.index_logic(i)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::truncate",
        spec: "\
            params: self, len\n\
            ensures: if len@ < self@.len() { (^self)@.len() == len@ } else { (^self)@ == self@ }",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::pop",
        spec: "\
            ensures: match result {\n\
                Some(t) => self@.len() > 0 && self@ == (^self)@.push_back(t),\n\
                None => self@.len() == 0 && (^self)@ == self@,\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::first",
        spec: "\
            ensures: match result {\n\
                Some(r) => self@.len() > 0 && *r == self@[0],\n\
                None => self@.len() == 0,\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::last",
        spec: "\
            ensures: match result {\n\
                Some(r) => self@.len() > 0 && *r == self@[self@.len() - 1],\n\
                None => self@.len() == 0,\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::swap",
        spec: "\
            params: self, a, b\n\
            requires: a@ < self@.len()\n\
            requires: b@ < self@.len()\n\
            ensures: (^self)@.len() == self@.len()\n\
            ensures: (^self)@.index_logic(a@) == self@.index_logic(b@)\n\
            ensures: (^self)@.index_logic(b@) == self@.index_logic(a@)",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::contains",
        spec: "\
            params: self, x\n\
            ensures: result == exists<i: Int> 0 <= i && i < self@.len() && self@.index_logic(i) == *x",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::resize",
        spec: "\
            params: self, new_len, value\n\
            ensures: (^self)@.len() == new_len@",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::swap_remove",
        spec: "\
            params: self, index\n\
            requires: index@ < self@.len()\n\
            ensures: result == self@[index@]\n\
            ensures: (^self)@.len() == self@.len() - 1",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::first_mut",
        spec: "\
            ensures: match result {\n\
                Some(r) => self@.len() > 0 && *r == self@.index_logic(0),\n\
                None => self@.len() == 0,\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::last_mut",
        spec: "\
            ensures: match result {\n\
                Some(r) => self@.len() > 0 && *r == self@.index_logic(self@.len() - 1),\n\
                None => self@.len() == 0,\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::as_mut_slice",
        spec: "ensures: result@ == self@",
    },
    // ── Vec<T> Index trait ──────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "<std::vec::Vec as core::ops::Index>::index",
        spec: "\
            params: self, ix\n\
            requires: ix.in_bounds(self@)\n\
            ensures: ix.has_value(self@, result)",
    },
    // ── Vec<T> IndexMut trait ───────────────────────────────────────
    BuiltinExternSpec {
        target_path: "<std::vec::Vec as core::ops::IndexMut>::index_mut",
        spec: "\
            params: self, ix\n\
            requires: ix.in_bounds(self@)\n\
            ensures: ix.has_value(self@, result)\n\
            ensures: ix.has_value((^self)@, ^result)\n\
            ensures: ix.resolve_elsewhere(self@, (^self)@)\n\
            ensures: (^self)@.len() == self@.len()",
    },
    // ── Option<T> ───────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "core::option::Option::is_some",
        spec: "ensures: result == self.is_some()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::is_none",
        spec: "ensures: result == !self.is_some()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::unwrap",
        spec: "\
            requires: self.is_some()\n\
            ensures: Some(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::expect",
        spec: "\
            requires: self.is_some()\n\
            ensures: Some(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::take",
        spec: "ensures: result == old(*self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::replace",
        spec: "ensures: result == old(*self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::map",
        spec: "ensures: self.is_none() ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::and_then",
        spec: "ensures: self.is_none() ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::unwrap_or",
        spec: "\
            params: self, default\n\
            ensures: self.is_none() ==> result == default",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::unwrap_or_default",
        spec: "\
            ensures: self.is_some() ==> Some(result) == old(self)\n\
            ensures: self.is_none() ==> result == Default::default()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::unwrap_or_else",
        spec: "\
            ensures: self.is_some() ==> Some(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::unwrap_unchecked",
        spec: "\
            requires: self.is_some()\n\
            ensures: Some(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::inspect",
        spec: "ensures: result == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::map_or",
        spec: "\
            params: self, default, f\n\
            ensures: self.is_none() ==> result == default",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::map_or_else",
        spec: "\
            params: self, default, f\n\
            ensures: self.is_none() ==> result == default()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::ok_or",
        spec: "\
            params: self, err\n\
            ensures: self.is_some() ==> result == Ok(old(self).unwrap())\n\
            ensures: self.is_none() ==> result == Err(err)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::ok_or_else",
        spec: "\
            params: self, err\n\
            ensures: self.is_some() ==> result == Ok(old(self).unwrap())\n\
            ensures: self.is_none() ==> result == Err(err())",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::as_ref",
        spec: "\
            ensures: self.is_some() ==> result.is_some()\n\
            ensures: self.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::as_mut",
        spec: "\
            ensures: self.is_some() ==> result.is_some()\n\
            ensures: self.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::and",
        spec: "\
            params: self, optb\n\
            ensures: self.is_none() ==> result == None\n\
            ensures: self.is_some() ==> result == optb",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::or",
        spec: "\
            params: self, optb\n\
            ensures: self.is_some() ==> result == old(self)\n\
            ensures: self.is_none() ==> result == optb",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::xor",
        spec: "\
            params: self, optb\n\
            ensures: self.is_some() && optb.is_none() ==> result == old(self)\n\
            ensures: self.is_none() && optb.is_some() ==> result == optb\n\
            ensures: self.is_some() && optb.is_some() ==> result == None\n\
            ensures: self.is_none() && optb.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::filter",
        spec: "ensures: self.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::is_some_and",
        spec: "ensures: self.is_none() ==> result == false",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::insert",
        spec: "\
            params: self, value\n\
            ensures: (^self) == Some(value)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::get_or_insert",
        spec: "\
            params: self, value\n\
            ensures: old(*self).is_some() ==> *result == old(*self).unwrap()\n\
            ensures: old(*self).is_none() ==> *result == value",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::get_or_insert_with",
        spec: "\
            ensures: old(*self).is_some() ==> *result == old(*self).unwrap()",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::take_if",
        spec: "ensures: old(*self).is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::copied",
        spec: "\
            ensures: self.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::cloned",
        spec: "\
            ensures: self.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::zip",
        spec: "\
            params: self, other\n\
            ensures: self.is_none() ==> result == None\n\
            ensures: other.is_none() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::unzip",
        spec: "\
            ensures: self.is_none() ==> result.0 == None && result.1 == None",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::transpose",
        spec: "ensures: self.is_none() ==> result == Ok(None)",
    },
    BuiltinExternSpec {
        target_path: "core::option::Option::flatten",
        spec: "ensures: self.is_none() ==> result == None",
    },
    // ── Result<T, E> ────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "core::result::Result::is_ok",
        spec: "ensures: result == self.is_ok()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::is_err",
        spec: "ensures: result == !self.is_ok()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::map",
        spec: "ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::and_then",
        spec: "ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap_or",
        spec: "\
            params: self, default\n\
            ensures: self.is_err() ==> result == default",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap",
        spec: "\
            requires: self.is_ok()\n\
            ensures: Ok(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::expect",
        spec: "\
            requires: self.is_ok()\n\
            ensures: Ok(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap_err",
        spec: "\
            requires: self.is_err()\n\
            ensures: Err(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::ok",
        spec: "\
            ensures: self.is_ok() ==> result == Some(old(self).unwrap())\n\
            ensures: self.is_err() ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::err",
        spec: "\
            ensures: self.is_ok() ==> result == None\n\
            ensures: self.is_err() ==> result == Some(old(self).unwrap_err())",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::map_err",
        spec: "ensures: self.is_ok() ==> result.is_ok()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap_or_else",
        spec: "\
            ensures: self.is_ok() ==> Ok(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::as_ref",
        spec: "\
            ensures: self.is_ok() ==> result.is_ok()\n\
            ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::as_mut",
        spec: "\
            ensures: self.is_ok() ==> result.is_ok()\n\
            ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::and",
        spec: "\
            params: self, res\n\
            ensures: self.is_ok() ==> result == res\n\
            ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::or",
        spec: "\
            params: self, res\n\
            ensures: self.is_ok() ==> result.is_ok()\n\
            ensures: self.is_err() ==> result == res",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::or_else",
        spec: "\
            params: self, op\n\
            ensures: self.is_ok() ==> result.is_ok()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap_or_default",
        spec: "\
            ensures: self.is_ok() ==> Ok(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::copied",
        spec: "\
            ensures: self.is_ok() ==> result.is_ok()\n\
            ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::cloned",
        spec: "\
            ensures: self.is_ok() ==> result.is_ok()\n\
            ensures: self.is_err() ==> result.is_err()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::transpose",
        spec: "\
            ensures: self.is_err() ==> result.is_some()",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::inspect",
        spec: "ensures: result == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::inspect_err",
        spec: "ensures: result == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::map_or",
        spec: "\
            params: self, default, f\n\
            ensures: self.is_err() ==> result == default",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::map_or_else",
        spec: "\
            params: self, default, f\n\
            ensures: self.is_err() ==> result == default(old(self).unwrap_err())",
    },
    // ── Clone for primitives ────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "<bool as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<i8 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<i16 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<i32 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<i64 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<i128 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<isize as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<u8 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<u16 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<u32 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<u64 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<u128 as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    BuiltinExternSpec {
        target_path: "<usize as core::clone::Clone>::clone",
        spec: "ensures: result == *self",
    },
    // ── Default for primitives ──────────────────────────────────────
    // All Default::default specs include `params:` (empty) because default()
    // takes no arguments. This suppresses "no parameter names" warnings from
    // cross-crate MIR lookup. (#2670)
    BuiltinExternSpec {
        target_path: "<bool as core::default::Default>::default",
        spec: "params:\nensures: result == false",
    },
    BuiltinExternSpec {
        target_path: "<i8 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<i16 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<i32 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<i64 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<i128 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<u8 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<u16 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<u32 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<u64 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<u128 as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<usize as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    BuiltinExternSpec {
        target_path: "<isize as core::default::Default>::default",
        spec: "params:\nensures: result == 0",
    },
    // ── Default for collections ────────────────────────────────────
    BuiltinExternSpec {
        target_path: "<std::collections::HashMap as core::default::Default>::default",
        spec: "params:\nensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "<std::collections::HashSet as core::default::Default>::default",
        spec: "params:\nensures: result@.len() == 0",
    },
    // ── Default for Vec, String, BTreeMap, BTreeSet ──────────────────
    BuiltinExternSpec {
        target_path: "<alloc::vec::Vec as core::default::Default>::default",
        spec: "params:\nensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "<alloc::string::String as core::default::Default>::default",
        spec: "params:\nensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "<alloc::collections::BTreeMap as core::default::Default>::default",
        spec: "params:\nensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "<alloc::collections::BTreeSet as core::default::Default>::default",
        spec: "params:\nensures: result@.len() == 0",
    },
    // ── String ──────────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::string::String::new",
        spec: "ensures: result.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::len",
        spec: "ensures: result@ >= self@.len()\nensures: self@.len() == 1 ==> result@ == self@.index_logic(0).to_utf8().len()",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::is_empty",
        spec: "ensures: result == (self.len() == 0)",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::clear",
        spec: "ensures: (^self).len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::capacity",
        spec: "ensures: result >= self.len()",
    },
    BuiltinExternSpec {
        target_path: "<std::string::String as core::convert::From<&str>>::from",
        spec: "\
            params: s\n\
            ensures: result@.len() == s@.len()\n\
            ensures: result@ == s@",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::as_str",
        spec: "ensures: result@ == self@",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::push_str",
        spec: "\
            params: self, string\n\
            ensures: (^self)@.len() == self@.len() + string@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::push",
        spec: "\
            params: self, ch\n\
            ensures: (^self)@ == self@.push_back(ch)",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::pop",
        spec: "ensures: self@.len() == 0 ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::contains",
        spec: "\
            params: self, pat",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::starts_with",
        spec: "\
            params: self, pat",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::ends_with",
        spec: "\
            params: self, pat",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::retain",
        spec: "\
            params: self, f\n\
            ensures: (^self).len() <= self.len()",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::insert",
        spec: "\
            params: self, idx, ch",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::insert_str",
        spec: "\
            params: self, idx, string",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::remove",
        spec: "\
            params: self, idx",
    },
    // ── Ordering ───────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "core::cmp::Ordering::then",
        spec: "\
            params: self, other\n\
            ensures: self != Ordering::Equal ==> result == self\n\
            ensures: self == Ordering::Equal ==> result == other",
    },
    BuiltinExternSpec {
        target_path: "core::cmp::Ordering::reverse",
        spec: "\
            ensures: self == Ordering::Less ==> result == Ordering::Greater\n\
            ensures: self == Ordering::Greater ==> result == Ordering::Less\n\
            ensures: self == Ordering::Equal ==> result == Ordering::Equal",
    },
    // ── Vec additional methods ──────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::vec::Vec::append",
        spec: "\
            params: self, other\n\
            ensures: (^self)@.len() == self@.len() + other@.len()\n\
            ensures: (^other)@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::split_off",
        spec: "\
            params: self, at\n\
            requires: at@ <= self@.len()\n\
            ensures: (^self)@.len() == at@\n\
            ensures: result@.len() == self@.len() - at@",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::retain",
        spec: "\
            params: self, f\n\
            ensures: (^self)@.len() <= self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::dedup",
        spec: "ensures: (^self)@.len() <= self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::reverse",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::sort",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::sort_unstable",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::as_slice",
        spec: "ensures: result@ == self@",
    },
    // ── String additional methods ───────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::string::String::truncate",
        spec: "\
            params: self, new_len\n\
            ensures: (^self).len() <= self.len()",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::reserve",
        spec: "\
            params: self, additional\n\
            ensures: (^self)@ == self@",
    },
    BuiltinExternSpec {
        target_path: "std::string::String::with_capacity",
        spec: "ensures: result@.len() == 0",
    },
    // ── BTreeMap ────────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::new",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::len",
        spec: "ensures: result@ == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::is_empty",
        spec: "ensures: result == (self@.len() == 0)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::insert",
        spec: "\
            params: self, k, v\n\
            ensures: (^self)@.contains(k)\n\
            ensures: (^self)@.lookup(k) == v",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::remove",
        spec: "\
            params: self, k\n\
            ensures: !(^self)@.contains(*k)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::get",
        spec: "\
            params: self, k\n\
            ensures: self@.contains(*k) ==> result.is_some()\n\
            ensures: !self@.contains(*k) ==> result == None",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::contains_key",
        spec: "\
            params: self, k\n\
            ensures: result == self@.contains(*k)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeMap::clear",
        spec: "ensures: (^self)@.len() == 0",
    },
    // ── BTreeSet ────────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::new",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::len",
        spec: "ensures: result@ == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::is_empty",
        spec: "ensures: result == (self@.len() == 0)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::insert",
        spec: "\
            ensures: (^self)@.contains(value)\n\
            ensures: result == !self@.contains(value)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::remove",
        spec: "\
            ensures: !(^self)@.contains(*value)\n\
            ensures: result == self@.contains(*value)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::contains",
        spec: "ensures: result == self@.contains(*value)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::BTreeSet::clear",
        spec: "ensures: (^self)@.len() == 0",
    },
    // ── HashMap ─────────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::new",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::with_capacity",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::len",
        spec: "ensures: result@ == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::is_empty",
        spec: "ensures: result == (self@.len() == 0)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::insert",
        spec: "\
            params: self, k, v\n\
            ensures: (^self)@.contains(k)\n\
            ensures: (^self)@.lookup(k) == v",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::remove",
        spec: "\
            params: self, k\n\
            ensures: !(^self)@.contains(*k)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::get",
        spec: "\
            params: self, k\n\
            ensures: match result {\n\
                Some(v) => self@.contains(*k) && *v == self@.lookup(*k),\n\
                None => !self@.contains(*k),\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::get_mut",
        spec: "\
            params: self, k\n\
            ensures: match result {\n\
                Some(v) => self@.contains(*k) && *v == self@.lookup(*k),\n\
                None => !self@.contains(*k),\n\
            }",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::contains_key",
        spec: "\
            params: self, k\n\
            ensures: result == self@.contains(*k)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::clear",
        spec: "ensures: (^self)@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashMap::retain",
        spec: "\
            params: self, f\n\
            ensures: (^self)@.len() <= self@.len()",
    },
    // ── HashSet ─────────────────────────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::new",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::with_capacity",
        spec: "ensures: result@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::len",
        spec: "ensures: result@ == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::is_empty",
        spec: "ensures: result == (self@.len() == 0)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::insert",
        spec: "\
            ensures: (^self)@.contains(value)\n\
            ensures: result == !self@.contains(value)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::remove",
        spec: "\
            ensures: !(^self)@.contains(*value)\n\
            ensures: result == self@.contains(*value)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::contains",
        spec: "ensures: result == self@.contains(*value)",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::clear",
        spec: "ensures: (^self)@.len() == 0",
    },
    BuiltinExternSpec {
        target_path: "std::collections::HashSet::retain",
        spec: "\
            params: self, f\n\
            ensures: (^self)@.len() <= self@.len()",
    },
    // ── Result expect_err / unsafe unwrap methods ────────────────────
    BuiltinExternSpec {
        target_path: "core::result::Result::expect_err",
        spec: "\
            requires: self.is_err()\n\
            ensures: Err(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap_unchecked",
        spec: "\
            requires: self.is_ok()\n\
            ensures: Ok(result) == old(self)",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::unwrap_err_unchecked",
        spec: "\
            requires: self.is_err()\n\
            ensures: Err(result) == old(self)",
    },
    // ── Result additional methods ──────────────────────────────────
    BuiltinExternSpec {
        target_path: "core::result::Result::is_ok_and",
        spec: "ensures: self.is_err() ==> result == false",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::is_err_and",
        spec: "ensures: self.is_ok() ==> result == false",
    },
    BuiltinExternSpec {
        target_path: "core::result::Result::flatten",
        spec: "ensures: self.is_err() ==> result.is_err()",
    },
    // ── Vec sort variant methods ───────────────────────────────────
    BuiltinExternSpec {
        target_path: "std::vec::Vec::sort_by",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::sort_by_key",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::sort_unstable_by",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    BuiltinExternSpec {
        target_path: "std::vec::Vec::sort_unstable_by_key",
        spec: "ensures: (^self)@.len() == self@.len()",
    },
    // ── NonZero types ──────────────────────────────────────────────
    //
    // NonZero::new returns Option<NonZero<T>>: Some when value != 0, None when 0.
    // NonZero::get returns the inner value, guaranteed non-zero.
    // NonZero::new_unchecked requires value != 0 (unsafe precondition).
    // All 12 concrete NonZero types (U8..Usize, I8..Isize) plus the generic
    // form (Rust 1.79+) share the same spec. (#2669, #2695)
    //
    // --- NonZero::new (generic Rust 1.79+) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZero::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    // --- NonZero::new (unsigned) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU8::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU16::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU32::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU64::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU128::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroUsize::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    // --- NonZero::new (signed) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI8::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI16::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI32::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI64::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI128::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroIsize::new",
        spec: "\
            params: value\n\
            ensures: value@ != 0 ==> result.is_some()\n\
            ensures: value@ != 0 ==> result.unwrap()@ == value@\n\
            ensures: value@ == 0 ==> result.is_none()",
    },
    // --- NonZero::get (generic Rust 1.79+) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZero::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    // --- NonZero::get (unsigned) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU8::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU16::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU32::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU64::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU128::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroUsize::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    // --- NonZero::get (signed) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI8::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI16::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI32::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI64::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI128::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroIsize::get",
        spec: "\
            ensures: result@ == self@\n\
            ensures: result@ != 0",
    },
    // --- NonZero::new_unchecked (generic Rust 1.79+) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZero::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    // --- NonZero::new_unchecked (unsigned) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU8::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU16::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU32::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU64::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroU128::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroUsize::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    // --- NonZero::new_unchecked (signed) ---
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI8::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI16::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI32::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI64::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroI128::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
    BuiltinExternSpec {
        target_path: "core::num::NonZeroIsize::new_unchecked",
        spec: "\
            params: value\n\
            requires: value@ != 0\n\
            ensures: result@ == value@",
    },
];

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::BUILTIN_EXTERN_SPECS;

    #[test]
    fn test_default_registry_covers_expected_primitive_surface() {
        let default_paths: BTreeSet<_> = BUILTIN_EXTERN_SPECS
            .iter()
            .filter(|entry| {
                entry
                    .target_path
                    .contains("core::default::Default>::default")
            })
            .map(|entry| entry.target_path)
            .collect();
        let expected_paths: BTreeSet<_> = [
            "<bool as core::default::Default>::default",
            "<i8 as core::default::Default>::default",
            "<i16 as core::default::Default>::default",
            "<i32 as core::default::Default>::default",
            "<i64 as core::default::Default>::default",
            "<i128 as core::default::Default>::default",
            "<isize as core::default::Default>::default",
            "<u8 as core::default::Default>::default",
            "<u16 as core::default::Default>::default",
            "<u32 as core::default::Default>::default",
            "<u64 as core::default::Default>::default",
            "<u128 as core::default::Default>::default",
            "<usize as core::default::Default>::default",
            "<std::collections::HashMap as core::default::Default>::default",
            "<std::collections::HashSet as core::default::Default>::default",
            "<alloc::vec::Vec as core::default::Default>::default",
            "<alloc::string::String as core::default::Default>::default",
            "<alloc::collections::BTreeMap as core::default::Default>::default",
            "<alloc::collections::BTreeSet as core::default::Default>::default",
        ]
        .into_iter()
        .collect();

        assert_eq!(default_paths, expected_paths);
    }

    #[test]
    fn test_nonzero_registry_covers_all_types_for_new_get_and_new_unchecked() {
        let nonzero_new_paths: BTreeSet<_> = BUILTIN_EXTERN_SPECS
            .iter()
            .filter(|entry| {
                entry.target_path.contains("NonZero") && entry.target_path.ends_with("::new")
            })
            .map(|entry| entry.target_path)
            .collect();
        let nonzero_get_paths: BTreeSet<_> = BUILTIN_EXTERN_SPECS
            .iter()
            .filter(|entry| {
                entry.target_path.contains("NonZero") && entry.target_path.ends_with("::get")
            })
            .map(|entry| entry.target_path)
            .collect();
        let nonzero_unchecked_paths: BTreeSet<_> = BUILTIN_EXTERN_SPECS
            .iter()
            .filter(|entry| {
                entry.target_path.contains("NonZero")
                    && entry.target_path.ends_with("::new_unchecked")
            })
            .map(|entry| entry.target_path)
            .collect();

        // 12 concrete types + 1 generic = 13 entries for new and get
        assert_eq!(nonzero_new_paths.len(), 13, "Expected 13 NonZero::new entries (12 concrete + 1 generic), got: {nonzero_new_paths:?}");
        assert_eq!(nonzero_get_paths.len(), 13, "Expected 13 NonZero::get entries (12 concrete + 1 generic), got: {nonzero_get_paths:?}");
        assert_eq!(nonzero_unchecked_paths.len(), 13, "Expected 13 NonZero::new_unchecked entries (12 concrete + 1 generic), got: {nonzero_unchecked_paths:?}");

        // Spot-check concrete types
        assert!(nonzero_new_paths.contains("core::num::NonZeroU32::new"));
        assert!(nonzero_new_paths.contains("core::num::NonZeroI64::new"));
        assert!(nonzero_get_paths.contains("core::num::NonZeroU32::get"));
        assert!(nonzero_get_paths.contains("core::num::NonZeroIsize::get"));
        assert!(nonzero_unchecked_paths.contains("core::num::NonZeroU32::new_unchecked"));
        assert!(nonzero_unchecked_paths.contains("core::num::NonZeroI64::new_unchecked"));

        // Verify generic paths (Rust 1.79+)
        assert!(nonzero_new_paths.contains("core::num::NonZero::new"));
        assert!(nonzero_get_paths.contains("core::num::NonZero::get"));
        assert!(nonzero_unchecked_paths.contains("core::num::NonZero::new_unchecked"));
    }

    #[test]
    fn vec_capacity_methods_preserve_len_and_elements() {
        for path in [
            "std::vec::Vec::reserve",
            "std::vec::Vec::reserve_exact",
            "std::vec::Vec::shrink_to_fit",
            "std::vec::Vec::shrink_to",
        ] {
            let spec = BUILTIN_EXTERN_SPECS
                .iter()
                .find(|entry| entry.target_path == path)
                .unwrap_or_else(|| panic!("missing built-in Vec capacity spec for {path}"))
                .spec;
            assert!(
                spec.contains("(^self)@.len() == self@.len()"),
                "{path} must preserve Vec view length"
            );
            assert!(
                spec.contains("forall<i: Int>")
                    && spec.contains("(^self)@.index_logic(i) == self@.index_logic(i)"),
                "{path} must preserve Vec elements"
            );
        }
    }
}
