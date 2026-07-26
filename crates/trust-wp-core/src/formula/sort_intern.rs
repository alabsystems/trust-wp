// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! String interner for `ExprSort::Datatype` names.
//!
//! Replaces heap-allocated `String` payloads with `u32` IDs, reducing
//! `ExprSort` from ~32 bytes (Clone) to ~8 bytes (Copy). This fixes the
//! stack overflow in deep recursive encodings (#2047) and eliminates
//! heap allocation on `ExprSort::clone()` for Datatype variants (#2055).
//!
//! Thread-safe via `OnceLock<Mutex<...>>`. The interner is append-only
//! and lives for the process lifetime.

use std::{
    collections::HashMap,
    sync::{Mutex, OnceLock},
};

static SORT_INTERNER: OnceLock<Mutex<SortInterner>> = OnceLock::new();

struct SortInterner {
    str_to_id: HashMap<String, u32>,
    id_to_str: Vec<String>,
}

impl SortInterner {
    fn new() -> Self {
        Self {
            str_to_id: HashMap::new(),
            id_to_str: Vec::new(),
        }
    }

    fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.str_to_id.get(s) {
            return id;
        }
        #[allow(clippy::cast_possible_truncation)] // Interner will never exceed u32::MAX entries
        let id = self.id_to_str.len() as u32;
        self.id_to_str.push(s.to_string());
        self.str_to_id.insert(s.to_string(), id);
        id
    }

    fn resolve(&self, id: u32) -> &str {
        &self.id_to_str[id as usize]
    }
}

fn interner() -> &'static Mutex<SortInterner> {
    SORT_INTERNER.get_or_init(|| Mutex::new(SortInterner::new()))
}

/// Intern a datatype name string, returning a stable `u32` ID.
///
/// The same string always returns the same ID within a process.
/// Used by `ExprSort::Datatype(u32)` to avoid heap-allocating sort names.
///
/// # Panics
///
/// Panics if the global sort interner mutex is poisoned.
#[must_use]
pub fn intern_sort_name(s: &str) -> u32 {
    interner().lock().expect("sort interner poisoned").intern(s)
}

/// Resolve an interned ID back to its original string.
///
/// Panics if the ID was not produced by `intern_sort_name`.
///
/// # Panics
///
/// Panics if the global sort interner mutex is poisoned or if `id` does not
/// refer to an interned sort name.
#[must_use]
pub fn resolve_sort_name(id: u32) -> String {
    interner()
        .lock()
        .expect("sort interner poisoned")
        .resolve(id)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_roundtrip() {
        let id = intern_sort_name("std::option::Option");
        assert_eq!(resolve_sort_name(id), "std::option::Option");
    }

    #[test]
    fn test_intern_dedup() {
        let id1 = intern_sort_name("MyStruct");
        let id2 = intern_sort_name("MyStruct");
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_intern_distinct() {
        let id1 = intern_sort_name("Foo_intern_test");
        let id2 = intern_sort_name("Bar_intern_test");
        assert_ne!(id1, id2);
    }
}
