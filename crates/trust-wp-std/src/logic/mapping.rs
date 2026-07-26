// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logical mapping (total function) type for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Mapping<A, B>` is a total function from `A` to `B`, used in specifications
//! and ghost code. Unlike partial functions, a `Mapping` returns a value for
//! every input — there is no "missing key" concept.
//!
//! At the SMT level, `Mapping<A, B>` is encoded as:
//! - An SMT array `(Array A B)` (SMT arrays are total functions)
//!
//! Key operations:
//! - `get(a)` — look up the value for key `a`
//! - `set(a, b)` — return a new mapping with `a` mapped to `b`
//! - `cst(b)` — create a constant mapping (every key maps to `b`)
//!
//! Runtime model: backed by a `HashMap<A, B>` for explicit entries plus a
//! default `B` value for unmapped keys. This is a test-time representation
//! only; the SMT encoding uses native array theory.
//!
//! Reference: Creusot's `creusot-std/src/logic/mapping.rs`

// Allow cast_sign_loss for Int to usize conversions in runtime model
#![allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
// Allow must_use for builder methods that chain
#![allow(clippy::must_use_candidate)]
// Builder pattern methods returning Self don't need must_use in logical model
#![allow(clippy::return_self_not_must_use)]
// Logical types use by-value semantics to match Creusot's Copy phantom types.
// Parameters are intentionally taken by value even when only used by reference.
#![allow(clippy::needless_pass_by_value)]

use std::{borrow::Borrow, collections::HashMap, hash::Hash};

/// A total function from `A` to `B` for use in specifications.
///
/// `Mapping<A, B>` models mathematical functions in specifications. Every
/// input has an output — there are no undefined values. In contracts:
///
/// ```text
/// #[ensures(result == Seq::create(n, |i| i * 2))]
/// fn even_numbers(n: Int) -> Seq<Int>
/// ```
///
/// In Creusot, `Mapping` is a `PhantomData`-backed zero-size type with
/// `#[builtin("map.Map.map")]`. Here we provide a runtime model for testing.
#[derive(Debug)]
#[must_use]
pub struct Mapping<A, B> {
    /// Explicit key-value entries
    entries: HashMap<A, B>,
    /// Default value for keys not in `entries`
    default: B,
}

impl<A, B> Mapping<A, B>
where
    A: Eq + Hash,
    B: Clone,
{
    /// Look up the value for key `a`.
    ///
    /// Since `Mapping` is a total function, this always returns a value.
    /// If `a` has been explicitly set, returns that value; otherwise returns
    /// the default.
    ///
    /// SMT encoding: `(select array a)` — SMT array select
    ///
    /// Creusot: `#[builtin("map.Map.get")]`
    pub fn get<Q>(&self, a: Q) -> B
    where
        Q: Borrow<A>,
    {
        self.entries
            .get(a.borrow())
            .cloned()
            .unwrap_or_else(|| self.default.clone())
    }

    /// Return a new mapping with `a` mapped to `b`.
    ///
    /// All other keys retain their previous values.
    ///
    /// SMT encoding: `(store array a b)` — SMT array store
    ///
    /// Creusot: `#[builtin("map.Map.set")]`
    pub fn set<K, V>(&self, a: K, b: V) -> Self
    where
        K: Into<A>,
        V: Into<B>,
        A: Clone,
    {
        let a: A = a.into();
        let b: B = b.into();
        let mut entries = self.entries.clone();
        entries.insert(a, b);
        Self {
            entries,
            default: self.default.clone(),
        }
    }

    /// Create a constant mapping where every key maps to `b`.
    ///
    /// SMT encoding: `((as const (Array A B)) b)` — SMT constant array
    ///
    /// Creusot: `#[builtin("map.Const.const")]`
    pub fn cst(b: B) -> Self {
        Self {
            entries: HashMap::new(),
            default: b,
        }
    }

    /// Create a mapping from a closure (compatibility shim).
    ///
    /// In Creusot, closure syntax can denote mappings in logical contexts.
    /// This runtime model does not execute the closure; it keeps a default map
    /// value sufficient for compilation and ghost-only typing.
    pub fn from_closure<F>(f: F) -> Self
    where
        B: Default,
        F: Fn(A) -> B,
    {
        let _ = f;
        Self::cst(B::default())
    }

    /// Extensional equality — two mappings are `ext_eq` if they produce
    /// the same output for every input.
    ///
    /// The runtime model checks all explicit entries from both sides against
    /// the other's value (falling back to default for missing keys), plus
    /// default equality. This correctly handles entries that match the other's
    /// default (e.g., `cst(0).set(3, 0)` equals `cst(0)`).
    ///
    /// SMT encoding: `map.MapExt.(==)`
    ///
    /// Creusot: `#[builtin("map.MapExt.(==)")]`
    pub fn ext_eq(self, other: Self) -> bool
    where
        B: PartialEq,
    {
        if self.default != other.default {
            return false;
        }
        // Check all keys in self
        for (k, v) in &self.entries {
            let other_v = other.entries.get(k).unwrap_or(&other.default);
            if v != other_v {
                return false;
            }
        }
        // Check keys in other that aren't in self
        for (k, v) in &other.entries {
            let self_v = self.entries.get(k).unwrap_or(&self.default);
            if v != self_v {
                return false;
            }
        }
        true
    }
}

impl<A, B> Clone for Mapping<A, B>
where
    A: Clone + Eq + Hash,
    B: Clone,
{
    fn clone(&self) -> Self {
        Self {
            entries: self.entries.clone(),
            default: self.default.clone(),
        }
    }
}

impl<A, B, F> From<F> for Mapping<A, B>
where
    A: Eq + Hash,
    B: Clone + Default,
    F: Fn(A) -> B,
{
    fn from(f: F) -> Self {
        Self::from_closure(f)
    }
}

impl<A, B> PartialEq for Mapping<A, B>
where
    A: Clone + Eq + Hash,
    B: PartialEq + Clone,
{
    fn eq(&self, other: &Self) -> bool {
        self.clone().ext_eq(other.clone())
    }
}

impl<A, B> Eq for Mapping<A, B>
where
    A: Clone + Eq + Hash,
    B: Eq + Clone,
{
}

/// Index implementation for `mapping[key]` syntax (Creusot compatibility).
///
/// Equivalent to `mapping.get(key)`.
///
/// DESIGN: `Box::leak` is intentional. The `Index` trait requires returning
/// `&Self::Output`, which must outlive `&self`. Since `get()` produces an owned
/// `B` (cloned from the internal `HashMap`), there is no stable storage to
/// reference. `Box::leak` converts the owned value into a `&'static B`.
///
/// This leaks one allocation per indexing call. Acceptable because:
/// - `Mapping` is a logical/ghost type used only in specifications and tests
/// - Test processes are short-lived; leaked memory is reclaimed at exit
/// - The alternative (internal `RefCell<Option<B>>` cache) adds runtime
///   complexity and only caches the *last* result, breaking concurrent reads
///
/// Do NOT use `mapping[key]` in hot loops; use `mapping.get(key)` instead.
impl<A, B> std::ops::Index<A> for Mapping<A, B>
where
    A: Clone + Eq + Hash,
    B: Clone,
{
    type Output = B;
    fn index(&self, key: A) -> &B {
        // Intentional leak — see DESIGN comment above. (#1410)
        Box::leak(Box::new(self.get(key)))
    }
}

/// Internal specification string constants consumed by trust-wp-driver's
/// table-backed logical lookup path and related local tests.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Mapping::get` (total function lookup)
    ///
    /// Total: every key has a value, no `contains` guard needed.
    /// Args: self=arg0, key=arg1
    pub const GET: &str = r"
        params: self, arg1
        ensures: result == self.get(arg1)
    ";

    /// Contract for `Mapping::set` (functional update, returns new mapping)
    ///
    /// Read-over-write axioms: same-key returns new value, other keys unchanged.
    /// Args: self=arg0, key=arg1, value=arg2
    pub const SET: &str = r"
        params: self, arg1, arg2
        ensures: result.get(arg1) == arg2
        ensures: forall<k2: _> k2 != arg1 ==> result.get(k2) == self.get(k2)
    ";

    /// Contract for `Mapping::cst` (constant mapping, associated function)
    ///
    /// Every key maps to the given value.
    /// Args: value=arg0 (no self)
    pub const CST: &str = r"
        params: arg0
        ensures: forall<k: _> result.get(k) == arg0
    ";

    /// Contract for `Mapping::ext_eq` (extensional equality)
    ///
    /// Two mappings are `ext_eq` iff they agree on every key.
    /// Args: self=arg0, other=arg1
    pub const EXT_EQ: &str = r"
        params: self, arg1
        ensures: result == forall<k: _> self.get(k) == arg1.get(k)
    ";

    /// Contract for `Mapping::index` (Index trait: `mapping[key]`)
    ///
    /// Delegates to `get`. Total: no precondition.
    /// Args: self=arg0, key=arg1
    pub const INDEX: &str = r"
        params: self, arg1
        ensures: *result == self.get(arg1)
    ";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mapping_cst() {
        let m: Mapping<i32, i32> = Mapping::cst(0);
        assert_eq!(m.clone().get(1), 0);
        assert_eq!(m.clone().get(42), 0);
        assert_eq!(m.get(-100), 0);
    }

    #[test]
    fn test_mapping_set_get() {
        let m: Mapping<i32, i32> = Mapping::cst(0);
        let m = m.set(1, 10).set(2, 20).set(3, 30);
        assert_eq!(m.clone().get(1), 10);
        assert_eq!(m.clone().get(2), 20);
        assert_eq!(m.clone().get(3), 30);
        assert_eq!(m.get(4), 0); // default
    }

    #[test]
    fn test_mapping_set_overwrite() {
        let m: Mapping<i32, i32> = Mapping::cst(0);
        let m = m.set(1, 10);
        assert_eq!(m.clone().get(1), 10);
        let m = m.set(1, 42);
        assert_eq!(m.get(1), 42);
    }

    #[test]
    fn test_mapping_ext_eq() {
        let m1: Mapping<i32, i32> = Mapping::cst(0).set(1, 10).set(2, 20);
        let m2: Mapping<i32, i32> = Mapping::cst(0).set(2, 20).set(1, 10);
        assert!(m1.clone().ext_eq(m2.clone()));

        // Explicitly setting default value should be ext_eq to not setting it
        let m3: Mapping<i32, i32> = Mapping::cst(0).set(1, 10).set(2, 20).set(3, 0);
        assert!(m1.ext_eq(m3));
    }

    #[test]
    fn test_mapping_ext_eq_different() {
        let m1: Mapping<i32, i32> = Mapping::cst(0).set(1, 10);
        let m2: Mapping<i32, i32> = Mapping::cst(0).set(1, 20);
        assert!(!m1.ext_eq(m2));
    }

    #[test]
    fn test_mapping_ext_eq_different_defaults() {
        let m1: Mapping<i32, i32> = Mapping::cst(0);
        let m2: Mapping<i32, i32> = Mapping::cst(1);
        assert!(!m1.ext_eq(m2));
    }

    #[test]
    fn test_mapping_clone() {
        let m: Mapping<i32, i32> = Mapping::cst(0).set(1, 10);
        let m2 = m.clone();
        assert_eq!(m.get(1), 10);
        assert_eq!(m2.get(1), 10);
    }

    #[test]
    fn test_mapping_partial_eq() {
        let m1: Mapping<i32, i32> = Mapping::cst(0).set(1, 10);
        let m2: Mapping<i32, i32> = Mapping::cst(0).set(1, 10);
        assert_eq!(m1, m2);
    }

    #[test]
    fn test_mapping_string_keys() {
        let m: Mapping<String, bool> = Mapping::cst(false);
        let m = m.set("hello".to_string(), true);
        let hello = "hello".to_string();
        assert!(m.clone().get("hello".to_string()));
        assert!(m.clone().get(&hello));
        assert!(!m.get("world".to_string()));
    }

    #[test]
    fn test_mapping_index_syntax() {
        // Tests the Index<A> implementation which uses Box::leak internally.
        // Each indexing call leaks a Box — this is accepted for Creusot
        // compatibility but should not be used in hot loops.
        let m: Mapping<i32, i32> = Mapping::cst(0).set(1, 10).set(2, 20);
        assert_eq!(m[1], 10, "Index should return value for key 1");
        assert_eq!(m[2], 20, "Index should return value for key 2");
        assert_eq!(m[99], 0, "Index should return default for missing key");
    }
}
