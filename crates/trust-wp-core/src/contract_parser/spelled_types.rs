// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type names a clause is read by their spelling.
//!
//! The parser has no scope: it reads a cast's target (`as u8`), a binder's
//! sort (`forall<x: Int>`), an annotation and a primitive path's head
//! (`u8::MAX`) by the NAME written. Rust reads the name through its scopes,
//! where an item, an import (a glob's included) or a generic parameter named
//! `u8` or `Int` hides the primitive or the prelude's model type. A name the
//! crate under verification gives such another meaning anywhere is refused
//! wherever a clause spells it there, as a bare constant name the crate gives
//! two meanings is (D-111): the parser cannot tell which scope a clause
//! stands in, and a guess reads the grant and the obligation one wrong way
//! (cast_target_*_shadows_primitive_granted.rs, D-202).
//!
//! A type name the parser does not read at all (`Byte`, `Self`, `Self::Out`)
//! gets no sort and no range. Where the crate binds it to a type that holds
//! a machine integer (an alias, an import, an associated type, an impl's
//! `Self`), a binder of it would range over the unbounded integers where Rust
//! ranges over the machine type's values
//! (quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs,
//! trait_contract_self_binder_inherited_by_machine_int_impl_granted.rs): such
//! a name is refused wherever a clause spells it as a type, by the same
//! crate-wide reading (D-205).
//!
//! A type reached by a path through a module or a crate
//! (`core::ffi::c_uchar`, `ffi::c_uchar` after `use core::ffi;`) names an
//! item of that module the parser cannot see and the crate need not bind,
//! an alias of a machine integer among them
//! (quantifier_binder_foreign_alias_path_of_machine_int_read_unbounded_granted.rs):
//! a written type holding a path whose head the crate binds to a module or
//! a crate, or `crate`, `self`, `super`, or a leading `::`, is refused, but
//! for a collection iterator the parser reads by its path (D-206). A path
//! off a generic parameter or `Self` (`T::Item`, `Self::Out`) is a
//! projection, not an item of a module.
//!
//! The driver installs the crate's sets before it parses any clause; with
//! none installed (the proc macros, unit tests) nothing is refused here.

use std::{
    collections::BTreeSet,
    sync::{Arc, PoisonError, RwLock},
};

/// Every name the parser gives one meaning by its spelling in a type
/// position or as a path's head: the primitive types, and the model and
/// collection names a binder's sort is read from.
pub const SPELLED_TYPE_NAMES: &[&str] = &[
    "bool", "char", "str", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64",
    "i128", "isize", "f32", "f64", "Int", "Bool", "Seq", "Vec", "hash_map", "hash_set",
];

static SHADOWED: RwLock<Option<Arc<BTreeSet<String>>>> = RwLock::new(None);

static MACHINE_INT_ALIASES: RwLock<Option<Arc<BTreeSet<String>>>> = RwLock::new(None);

static MODULES: RwLock<Option<Arc<BTreeSet<String>>>> = RwLock::new(None);

/// Whether the parser reads `name` by its spelling.
#[must_use]
pub fn is_spelled_type_name(name: &str) -> bool {
    SPELLED_TYPE_NAMES.contains(&name)
}

/// Install the spelled names the crate under verification gives another
/// meaning (see the module documentation).
pub fn install_shadowed_type_names(names: BTreeSet<String>) {
    let mut guard = SHADOWED.write().unwrap_or_else(PoisonError::into_inner);
    *guard = Some(Arc::new(names));
}

/// Install the names the crate under verification binds to a type that
/// holds a machine integer the parser cannot see (D-205).
pub fn install_machine_int_alias_names(names: BTreeSet<String>) {
    let mut guard = MACHINE_INT_ALIASES
        .write()
        .unwrap_or_else(PoisonError::into_inner);
    *guard = Some(Arc::new(names));
}

/// Install the names the crate under verification binds to a module or a
/// crate (D-206).
pub fn install_module_names(names: BTreeSet<String>) {
    let mut guard = MODULES.write().unwrap_or_else(PoisonError::into_inner);
    *guard = Some(Arc::new(names));
}

/// Forget the installed sets (a new crate, or the end of a session).
pub fn clear_shadowed_type_names() {
    let mut guard = SHADOWED.write().unwrap_or_else(PoisonError::into_inner);
    *guard = None;
    let mut guard = MACHINE_INT_ALIASES
        .write()
        .unwrap_or_else(PoisonError::into_inner);
    *guard = None;
    let mut guard = MODULES.write().unwrap_or_else(PoisonError::into_inner);
    *guard = None;
}

/// The first identifier `text` spells that the installed set holds.
pub(crate) fn first_shadowed(text: &str) -> Option<String> {
    let guard = SHADOWED.read().unwrap_or_else(PoisonError::into_inner);
    first_shadowed_in(guard.as_deref()?, text)
}

/// The first identifier `text` spells that the crate binds to a type holding
/// a machine integer the parser cannot see.
pub(crate) fn first_machine_int_alias(text: &str) -> Option<String> {
    let guard = MACHINE_INT_ALIASES
        .read()
        .unwrap_or_else(PoisonError::into_inner);
    first_shadowed_in(guard.as_deref()?, text)
}

/// The first path `text` writes through a module or a crate, by the
/// installed set (D-206).
pub(crate) fn first_module_path(text: &str) -> Option<String> {
    let guard = MODULES.read().unwrap_or_else(PoisonError::into_inner);
    first_module_path_in(guard.as_deref()?, text)
}

/// The first shadowed name of a path's HEAD (`u8` of `u8::MAX`), or of any
/// type a qualified path (`<u8 as Tr>::m`) writes, by the installed set.
pub(crate) fn shadowed_path_head(path: &str) -> Option<String> {
    let guard = SHADOWED.read().unwrap_or_else(PoisonError::into_inner);
    shadowed_path_head_in(guard.as_deref()?, path)
}

fn first_shadowed_in(names: &BTreeSet<String>, text: &str) -> Option<String> {
    text.split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
        .filter(|word| !word.is_empty() && !word.starts_with(|ch: char| ch.is_ascii_digit()))
        .find(|word| names.contains(*word))
        .map(str::to_string)
}

/// A path a written type spells: its segments, and whether it starts with
/// `::` (an extern crate's root).
struct WrittenPath {
    rooted: bool,
    segments: Vec<String>,
}

impl WrittenPath {
    fn spelled(&self) -> String {
        let joined = self.segments.join("::");
        if self.rooted {
            format!("::{joined}")
        } else {
            joined
        }
    }
}

fn first_module_path_in(modules: &BTreeSet<String>, text: &str) -> Option<String> {
    written_paths(text)
        .into_iter()
        .find(|path| {
            let Some(head) = path.segments.first() else {
                return path.rooted;
            };
            if path.rooted {
                return true;
            }
            path.segments.len() > 1
                && (matches!(head.as_str(), "crate" | "self" | "super") || modules.contains(head))
                && super::helpers::quantifiers::collection_iterator_sort(&path.segments).is_none()
        })
        .map(|path| path.spelled())
}

/// Every maximal `ident (:: ident)*` path of `text`, a leading `::` kept as
/// `rooted`. A generic argument list (`<..>`) ends a path, and each path
/// inside it is its own.
fn written_paths(text: &str) -> Vec<WrittenPath> {
    let chars: Vec<char> = text.chars().collect();
    let is_start = |ch: char| ch.is_alphabetic() || ch == '_';
    let is_continue = |ch: char| ch.is_alphanumeric() || ch == '_';
    let skip_ws = |mut at: usize| {
        while chars.get(at).is_some_and(|ch| ch.is_whitespace()) {
            at += 1;
        }
        at
    };
    let separator_at = |at: usize| chars.get(at) == Some(&':') && chars.get(at + 1) == Some(&':');
    let ident_at = |at: usize| -> Option<(String, usize)> {
        let first = *chars.get(at)?;
        if !is_start(first) || (at > 0 && chars[at - 1] == '\'') {
            return None;
        }
        let mut end = at + 1;
        while chars.get(end).copied().is_some_and(is_continue) {
            end += 1;
        }
        Some((chars[at..end].iter().collect(), end))
    };
    // A `::` after a word or a `>` continues what precedes it (`Vec::<u8>`),
    // and roots nothing.
    let continues = |at: usize| {
        chars[..at]
            .iter()
            .rev()
            .find(|ch| !ch.is_whitespace())
            .is_some_and(|&ch| is_continue(ch) || ch == '>')
    };
    let mut paths = Vec::new();
    let mut at = 0;
    while at < chars.len() {
        let separator = separator_at(at);
        if separator && continues(at) {
            at += 2;
            continue;
        }
        let rooted = separator;
        let head_at = if rooted { skip_ws(at + 2) } else { at };
        let Some((head, mut end)) = ident_at(head_at) else {
            if rooted {
                paths.push(WrittenPath {
                    rooted,
                    segments: Vec::new(),
                });
                at += 2;
            } else if chars[at].is_alphanumeric() || chars[at] == '_' {
                // The tail of a word that is not an identifier (`4u8`, `'a`).
                while chars.get(at).copied().is_some_and(is_continue) {
                    at += 1;
                }
            } else {
                at += 1;
            }
            continue;
        };
        let mut segments = vec![head];
        loop {
            let separator = skip_ws(end);
            if !separator_at(separator) {
                break;
            }
            let Some((segment, next)) = ident_at(skip_ws(separator + 2)) else {
                break;
            };
            segments.push(segment);
            end = next;
        }
        paths.push(WrittenPath { rooted, segments });
        at = end;
    }
    paths
}

/// A single segment is a value name, never a type the parser reads.
fn shadowed_path_head_in(names: &BTreeSet<String>, path: &str) -> Option<String> {
    let path = path.trim();
    if path.starts_with('<') {
        return first_shadowed_in(names, path);
    }
    let (head, _) = path.split_once("::")?;
    first_shadowed_in(names, head)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_spelled_name_is_found_as_a_word_and_a_path_by_its_head() {
        let names = BTreeSet::from(["u8".to_string(), "Int".to_string()]);
        assert_eq!(first_shadowed_in(&names, "u8").as_deref(), Some("u8"));
        assert_eq!(first_shadowed_in(&names, "Seq<u8>").as_deref(), Some("u8"));
        assert_eq!(
            first_shadowed_in(&names, "&mut Int").as_deref(),
            Some("Int")
        );
        assert_eq!(first_shadowed_in(&names, "u16"), None);
        assert_eq!(first_shadowed_in(&names, "u8x"), None);
        assert_eq!(
            shadowed_path_head_in(&names, "u8::MAX").as_deref(),
            Some("u8")
        );
        assert_eq!(shadowed_path_head_in(&names, "core::u8::MAX"), None);
        assert_eq!(shadowed_path_head_in(&names, "u8"), None);
        assert_eq!(
            shadowed_path_head_in(&names, "<u8 as Tr>::m").as_deref(),
            Some("u8")
        );
        assert!(SPELLED_TYPE_NAMES
            .iter()
            .all(|name| is_spelled_type_name(name)));
    }

    #[test]
    fn a_path_through_a_module_or_a_crate_is_found_and_a_projection_is_not() {
        let modules = BTreeSet::from([
            "core".to_string(),
            "ffi".to_string(),
            "hash_map".to_string(),
        ]);
        let found = |text: &str| first_module_path_in(&modules, text);
        assert_eq!(
            found("core::ffi::c_uchar").as_deref(),
            Some("core::ffi::c_uchar")
        );
        assert_eq!(found("ffi::c_uchar").as_deref(), Some("ffi::c_uchar"));
        assert_eq!(found("ffi :: c_uchar").as_deref(), Some("ffi::c_uchar"));
        assert_eq!(
            found("&core::ffi::c_uchar").as_deref(),
            Some("core::ffi::c_uchar")
        );
        assert_eq!(found("Seq<ffi::c_uchar>").as_deref(), Some("ffi::c_uchar"));
        assert_eq!(found("crate::m::Byte").as_deref(), Some("crate::m::Byte"));
        assert_eq!(found("super::Byte").as_deref(), Some("super::Byte"));
        assert_eq!(
            found("::core::ffi::c_int").as_deref(),
            Some("::core::ffi::c_int")
        );
        assert_eq!(found("K::DeepModelTy"), None);
        assert_eq!(found("Self::Out"), None);
        assert_eq!(found("&mut hash_map::IntoIter<K, V>"), None);
        assert_eq!(
            found("hash_map::IntoIter<K, ffi::c_uchar>").as_deref(),
            Some("ffi::c_uchar")
        );
        assert_eq!(found("[u8; 4]"), None);
        assert_eq!(found("&'static u8"), None);
        assert_eq!(found("Seq<T>"), None);
        assert_eq!(found("ffi"), None);
        assert_eq!(found("Vec::<u8>"), None);
        assert_eq!(
            found("Seq::<ffi::c_uchar>").as_deref(),
            Some("ffi::c_uchar")
        );
    }
}
