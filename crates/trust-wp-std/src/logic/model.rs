// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! View trait for specification models
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The `View` trait provides a way to convert runtime types to their logical
//! specification models. For example:
//! - `Vec<T>` views as `Seq<T>` (logical sequence)
//! - `i32` views as `Int` (unbounded integer)
//!
//! This enables writing contracts that reason about values without machine
//! integer overflow concerns or collection implementation details.
//!
//! # Creusot Compatibility
//!
//! This trait follows Creusot's View pattern (source: `creusot-std/src/model.rs`).
//! In Creusot, the `@` postfix operator is syntactic sugar for `.view()`:
//!
//! ```text
//! v@       // Creusot syntax
//! v.view() // Equivalent
//! ```
//!
//! trust-wp supports both `view(x)` function syntax and the `@` postfix
//! operator (transformed by `trust-wp-macros/src/view_syntax.rs`).
//!
//! # Example
//!
//! ```text
//! #[ensures(result.view() == self.view().push_back(value))]
//! fn push(&mut self, value: T);
//! ```

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    hash::Hash,
};

use super::{FMap, FSet, Int, Seq};
use crate::ghost::Snapshot;

/// Trait for converting runtime types to their specification models.
///
/// The `View` trait defines how runtime values map to their logical
/// representations for use in contracts and specifications.
///
/// # Associated Type
///
/// - `ViewTy`: The logical model type (e.g., `Int`, `Seq<T>`)
///
/// # Example
///
/// ```text
/// // Vec<T> views as Seq<T>
/// impl<T> View for Vec<T> {
///     type ViewTy = Seq<T>;
///     fn view(self) -> Seq<T> { /* ... */ }
/// }
///
/// // i32 views as Int (unbounded integer)
/// impl View for i32 {
///     type ViewTy = Int;
///     fn view(self) -> Int { Int::from(self) }
/// }
/// ```
pub trait View {
    /// The logical model type for this runtime type.
    type ViewTy;

    /// Convert this value to its logical model.
    ///
    /// In specifications, this allows reasoning about values without
    /// implementation details or overflow concerns.
    ///
    /// `view` is a logic-mode method in Creusot's design — implementers
    /// override with `#[logic(open)]` or `#[logic(opaque)]`. The
    /// trait/impl consistency checker enforces this.
    #[crate::logic(open)]
    fn view(self) -> Self::ViewTy;
}

// Creusot code routinely applies `@` through borrowed values. Keep a shared
// reference blanket so any owned logical carrier that already implements
// `View` is transparently usable behind `&T`.
impl<T: View + ?Sized> View for &T {
    type ViewTy = T::ViewTy;

    fn view(self) -> Self::ViewTy {
        panic!("View::view on shared reference is specification-only")
    }
}

// Mutable references should preserve the same logical model as the owned
// carrier, matching Creusot's reference-transparent `@` behavior.
impl<T: View + ?Sized> View for &mut T {
    type ViewTy = T::ViewTy;

    fn view(self) -> Self::ViewTy {
        panic!("View::view on mutable reference is specification-only")
    }
}

// =============================================================================
// View implementations for bool and char
// =============================================================================

/// View for `bool` is identity — booleans are their own logical model.
///
/// Reference: Creusot `creusot-contracts/src/model.rs` (bool: View<ViewTy=bool>)
impl View for bool {
    type ViewTy = bool;

    fn view(self) -> bool {
        self
    }
}

/// View for `char` is identity — characters are their own logical model.
///
/// Reference: Creusot `creusot-contracts/src/model.rs` (char: View<ViewTy=char>)
impl View for char {
    type ViewTy = char;

    fn view(self) -> char {
        self
    }
}

// =============================================================================
// View implementations for primitive integer types
// =============================================================================

impl View for i8 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for i16 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for i32 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for i64 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for i128 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for isize {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for u8 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for u16 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for u32 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for u64 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

impl View for usize {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

/// View implementation for u128.
///
/// `Int` currently uses `i128` in host Rust code. `u128` values above
/// `i128::MAX` are rejected with panic instead of silently truncating.
/// This keeps runtime/spec conversion failures explicit.
impl View for u128 {
    type ViewTy = Int;

    fn view(self) -> Int {
        Int::from(self)
    }
}

// =============================================================================
// View implementation for Vec<T>
// =============================================================================

impl<T> View for Vec<T> {
    type ViewTy = Seq<T>;

    fn view(self) -> Seq<T> {
        Seq::from(self)
    }
}

// =============================================================================
// View implementation for HashMap<K, V>
// =============================================================================

impl<K, V> View for HashMap<K, V>
where
    K: Eq + Hash,
{
    type ViewTy = FMap<K, V>;

    fn view(self) -> FMap<K, V> {
        FMap::from(self)
    }
}

// =============================================================================
// View implementation for HashSet<T>
// =============================================================================

/// View for `HashSet<T>` maps to `FSet<T>`, matching Creusot's set view.
///
/// Reference: Creusot `creusot-std/src/std/collections/hash_set.rs`
impl<T> View for HashSet<T>
where
    T: Eq + Hash,
{
    type ViewTy = FSet<T>;

    fn view(self) -> FSet<T> {
        FSet::from(self)
    }
}

// =============================================================================
// View implementation for BTreeMap<K, V>
// =============================================================================

/// View for `BTreeMap<K, V>` maps to `FMap<K, V>`.
///
/// BTreeMap and HashMap both model as FMap at the specification level.
/// The ordering constraint on BTreeMap is a runtime property, not a
/// logical one — both map types share the same logical model.
impl<K, V> View for BTreeMap<K, V>
where
    K: Ord + Eq + Hash,
{
    type ViewTy = FMap<K, V>;

    fn view(self) -> FMap<K, V> {
        FMap::from(self)
    }
}

// =============================================================================
// View implementation for BTreeSet<T>
// =============================================================================

/// View for `BTreeSet<T>` maps to `FSet<T>`.
///
/// Same logical model as `HashSet<T>` — ordering is a runtime property.
impl<T> View for BTreeSet<T>
where
    T: Ord + Eq + Hash,
{
    type ViewTy = FSet<T>;

    fn view(self) -> FSet<T> {
        FSet::from(self)
    }
}

// =============================================================================
// View implementation for VecDeque<T>
// =============================================================================

/// View for `VecDeque<T>` maps to `Seq<T>`, matching Creusot's deque view.
///
/// At the specification level, a deque is a sequence — the ring-buffer
/// implementation detail is irrelevant for logical reasoning.
///
/// Reference: Creusot `creusot-std/src/std/deque.rs`
impl<T> View for VecDeque<T> {
    type ViewTy = Seq<T>;

    fn view(self) -> Seq<T> {
        Seq::from(self.into_iter().collect::<Vec<T>>())
    }
}

// Snapshot values are viewable in specification contexts.
impl<T: View> View for Snapshot<T> {
    type ViewTy = T::ViewTy;

    fn view(self) -> Self::ViewTy {
        panic!("Snapshot::view is specification-only")
    }
}

// =============================================================================
// View implementation for Option<T> and Result<T, E>
// =============================================================================

/// View for `Option<T>` is identity — in specs, Option values are used directly.
/// The `@` operator on an Option is a no-op.
///
/// Reference: Creusot `creusot-contracts/src/model.rs`
impl<T> View for Option<T> {
    type ViewTy = Option<T>;

    fn view(self) -> Option<T> {
        self
    }
}

/// View for `Result<T, E>` is identity — in specs, Result values are used directly.
///
/// Reference: Creusot `creusot-contracts/src/model.rs`
impl<T, E> View for Result<T, E> {
    type ViewTy = Result<T, E>;

    fn view(self) -> Result<T, E> {
        self
    }
}

// =============================================================================
// View implementation for Box<T>
// =============================================================================

/// View for `Box<T>` delegates to T's View — boxes are transparent in specs.
///
/// Reference: Creusot `creusot-contracts/src/model.rs`
impl<T: View> View for Box<T> {
    type ViewTy = T::ViewTy;

    fn view(self) -> T::ViewTy {
        (*self).view()
    }
}

/// View for `Rc<T>` is identity.
///
/// Creusot examples use `*rc@` as a logical handle to the pointee allocation,
/// notably when `Rc<PermCell<_>>` values are used as permission-map keys. An
/// identity view preserves the `Rc` deref step in those expressions.
impl<T> View for std::rc::Rc<T> {
    type ViewTy = Self;

    fn view(self) -> Self {
        panic!("View for Rc<T> is specification-only")
    }
}

// =============================================================================
// View implementation for tuples
// =============================================================================

/// View for tuples applies View to each element.
///
/// Reference: Creusot `creusot-contracts/src/model.rs`
macro_rules! view_tuple {
    ($(($($T:ident : $idx:tt),+)),*) => {
        $(impl<$($T: View),+> View for ($($T,)+) {
            type ViewTy = ($($T::ViewTy,)+);
            fn view(self) -> Self::ViewTy {
                ($(self.$idx.view(),)+)
            }
        })*
    };
}

view_tuple!(
    (A: 0),
    (A: 0, B: 1),
    (A: 0, B: 1, C: 2),
    (A: 0, B: 1, C: 2, D: 3),
    (A: 0, B: 1, C: 2, D: 3, E: 4),
    (A: 0, B: 1, C: 2, D: 3, E: 4, F: 5)
);

// =============================================================================
// View implementation for fixed-size arrays
// =============================================================================

/// View for `[T; N]` maps to `Seq<T>`, matching slice View semantics.
impl<T, const N: usize> View for [T; N] {
    type ViewTy = Seq<T>;

    fn view(self) -> Seq<T> {
        panic!("View::view on fixed-size array is specification-only")
    }
}

// =============================================================================
// View implementation for slices
// =============================================================================

impl<T> View for &[T] {
    type ViewTy = Seq<T>;

    fn view(self) -> Seq<T> {
        // Specification-only: Creusot's `[T].view()` is a built-in that
        // doesn't require Clone. We panic since this is never called at
        // runtime in verification context.
        panic!("View for &[T] is specification-only")
    }
}

impl<T> View for &mut [T] {
    type ViewTy = Seq<T>;

    fn view(self) -> Seq<T> {
        // Specification-only: see above.
        panic!("View for &mut [T] is specification-only")
    }
}

// =============================================================================
// View implementation for str and String
// =============================================================================

/// View for `&str` maps to `Seq<char>`, matching Creusot's `str` view.
///
/// In Creusot, `View` is implemented for unsized `str` directly, but our
/// `View` trait takes `self` by value (Sized bound). We implement it for
/// `&str` instead, which is how it's actually used in contracts (`s@`).
///
/// Reference: Creusot `creusot-std/src/std/string.rs:5-12`
impl View for &str {
    type ViewTy = Seq<char>;

    fn view(self) -> Seq<char> {
        Seq::from(self.chars().collect::<Vec<char>>())
    }
}

/// View for `String` maps to `Seq<char>`.
impl View for String {
    type ViewTy = Seq<char>;

    fn view(self) -> Seq<char> {
        Seq::from(self.chars().collect::<Vec<char>>())
    }
}

// =============================================================================
// View implementation for Int and Seq (identity)
// =============================================================================

impl View for Int {
    type ViewTy = Int;

    fn view(self) -> Int {
        self
    }
}

impl<T> View for Seq<T> {
    type ViewTy = Seq<T>;

    fn view(self) -> Seq<T> {
        self
    }
}

impl<K, V> View for FMap<K, V> {
    type ViewTy = FMap<K, V>;

    fn view(self) -> FMap<K, V> {
        self
    }
}

impl<T> View for FSet<T> {
    type ViewTy = FSet<T>;

    fn view(self) -> FSet<T> {
        self
    }
}

// =============================================================================
// Helper function for contracts
// =============================================================================

/// Convert a value to its logical view.
///
/// This is a convenience function for use in contracts. It's equivalent to
/// calling `.view()` on the value.
///
/// # Example
///
/// ```text
/// #[ensures(view(result) == view(self).push_back(value))]
/// fn push(&mut self, value: T);
/// ```
///
/// The `@` postfix operator is also supported (see
/// `trust-wp-macros/src/view_syntax.rs`):
/// ```text
/// #[ensures(result@ == self@.push_back(value))]
/// fn push(&mut self, value: T);
/// ```
#[inline]
pub fn view<T: View>(value: T) -> T::ViewTy {
    value.view()
}

// =============================================================================
// DeepModel trait (Creusot compatibility)
// =============================================================================

/// Deep model for specification of equality, ordering, and hash operations.
///
/// Unlike `View` (which is a shallow conversion), `DeepModel` recursively
/// transforms contained types through their own `deep_model()`. This is used
/// for specifying operations like `PartialEq`, `Ord`, and `Hash` that depend
/// on the logical identity of contained elements.
///
/// # Example
///
/// ```text
/// // Vec<i32>.view()       -> Seq<i32>  (elements stay as i32)
/// // Vec<i32>.deep_model() -> Seq<Int>  (elements become Int)
/// ```
///
/// Source: Creusot `creusot-std/src/model.rs:26-30`
pub trait DeepModel {
    /// The deep model type.
    type DeepModelTy;

    /// Convert this value to its deep logical model.
    ///
    /// Logic-mode in Creusot's design — implementers override with
    /// `#[logic(open)]`.
    #[crate::logic(open)]
    fn deep_model(self) -> Self::DeepModelTy;
}

// --- DeepModel: identity types ---

impl DeepModel for bool {
    type DeepModelTy = bool;
    fn deep_model(self) -> bool {
        self
    }
}

impl DeepModel for Int {
    type DeepModelTy = Int;
    fn deep_model(self) -> Int {
        self
    }
}

impl DeepModel for core::cmp::Ordering {
    type DeepModelTy = core::cmp::Ordering;
    fn deep_model(self) -> core::cmp::Ordering {
        self
    }
}

impl DeepModel for () {
    type DeepModelTy = ();
    fn deep_model(self) {}
}

// --- DeepModel: machine integers -> Int ---

macro_rules! deep_model_int {
    ($($t:ty),*) => {
        $(impl DeepModel for $t {
            type DeepModelTy = Int;
            fn deep_model(self) -> Int {
                self.view()
            }
        })*
    };
}

deep_model_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl DeepModel for char {
    type DeepModelTy = Int;
    fn deep_model(self) -> Int {
        Int::from(self as i128)
    }
}

// --- DeepModel: references (delegation) ---

impl<T: DeepModel + Clone> DeepModel for &T {
    type DeepModelTy = T::DeepModelTy;
    fn deep_model(self) -> T::DeepModelTy {
        self.clone().deep_model()
    }
}

impl<T: DeepModel + Clone> DeepModel for &mut T {
    type DeepModelTy = T::DeepModelTy;
    fn deep_model(self) -> T::DeepModelTy {
        self.clone().deep_model()
    }
}

// --- DeepModel: collections (deep recursion) ---

impl<T: DeepModel + Clone> DeepModel for Vec<T> {
    type DeepModelTy = Seq<T::DeepModelTy>;
    fn deep_model(self) -> Seq<T::DeepModelTy> {
        panic!("DeepModel::deep_model on Vec<T> is specification-only")
    }
}

impl<T: DeepModel + Clone> DeepModel for Option<T> {
    type DeepModelTy = Option<T::DeepModelTy>;
    fn deep_model(self) -> Option<T::DeepModelTy> {
        self.map(DeepModel::deep_model)
    }
}

impl<T: DeepModel + Clone, E: DeepModel + Clone> DeepModel for Result<T, E> {
    type DeepModelTy = Result<T::DeepModelTy, E::DeepModelTy>;
    fn deep_model(self) -> Result<T::DeepModelTy, E::DeepModelTy> {
        match self {
            Ok(v) => Ok(v.deep_model()),
            Err(e) => Err(e.deep_model()),
        }
    }
}

// --- DeepModel: tuples ---

macro_rules! deep_model_tuple {
    ($(($($T:ident : $idx:tt),+)),*) => {
        $(impl<$($T: DeepModel),+> DeepModel for ($($T,)+) {
            type DeepModelTy = ($($T::DeepModelTy,)+);
            fn deep_model(self) -> Self::DeepModelTy {
                ($(self.$idx.deep_model(),)+)
            }
        })*
    };
}

deep_model_tuple!(
    (A: 0),
    (A: 0, B: 1),
    (A: 0, B: 1, C: 2),
    (A: 0, B: 1, C: 2, D: 3),
    (A: 0, B: 1, C: 2, D: 3, E: 4),
    (A: 0, B: 1, C: 2, D: 3, E: 4, F: 5)
);

// --- DeepModel: String ---

/// DeepModel for `String` maps to `Seq<Int>` — each char becomes its Int code point.
///
/// Reference: Creusot `creusot-contracts/src/model.rs`
impl DeepModel for String {
    type DeepModelTy = Seq<Int>;
    fn deep_model(self) -> Seq<Int> {
        Seq::from(
            self.chars()
                .map(|c| Int::from(c as i128))
                .collect::<Vec<Int>>(),
        )
    }
}

// --- DeepModel: &str ---

/// DeepModel for `&str` maps to `Seq<Int>` — each char becomes its Int code point.
///
/// Mirrors `DeepModel for String` but works directly on borrowed str slices,
/// which is how string values appear in many contract contexts.
impl DeepModel for &str {
    type DeepModelTy = Seq<Int>;
    fn deep_model(self) -> Seq<Int> {
        Seq::from(
            self.chars()
                .map(|c| Int::from(c as i128))
                .collect::<Vec<Int>>(),
        )
    }
}

// --- DeepModel: slices ---

/// DeepModel for `&[T]` maps to `Seq<T::DeepModelTy>`.
///
/// Reference: Creusot `creusot-std/src/std/slice.rs`
impl<T: DeepModel + Clone> DeepModel for &[T] {
    type DeepModelTy = Seq<T::DeepModelTy>;
    fn deep_model(self) -> Seq<T::DeepModelTy> {
        panic!("DeepModel::deep_model on &[T] is specification-only")
    }
}

/// DeepModel for `&mut [T]` maps to `Seq<T::DeepModelTy>`.
impl<T: DeepModel + Clone> DeepModel for &mut [T] {
    type DeepModelTy = Seq<T::DeepModelTy>;
    fn deep_model(self) -> Seq<T::DeepModelTy> {
        panic!("DeepModel::deep_model on &mut [T] is specification-only")
    }
}

// --- DeepModel: HashMap / HashSet ---

/// DeepModel for `HashMap<K, V>` recursively applies DeepModel to keys and values.
///
/// This mirrors how Creusot's HashMap deep_model works: the result is an
/// FMap keyed on K::DeepModelTy containing V::DeepModelTy values.
impl<K, V> DeepModel for HashMap<K, V>
where
    K: DeepModel + Eq + Hash,
    K::DeepModelTy: Eq + Hash,
    V: DeepModel,
{
    type DeepModelTy = FMap<K::DeepModelTy, V::DeepModelTy>;
    fn deep_model(self) -> FMap<K::DeepModelTy, V::DeepModelTy> {
        panic!("DeepModel::deep_model on HashMap is specification-only")
    }
}

/// DeepModel for `HashSet<T>` recursively applies DeepModel to elements.
impl<T> DeepModel for HashSet<T>
where
    T: DeepModel + Eq + Hash,
    T::DeepModelTy: Eq + Hash,
{
    type DeepModelTy = FSet<T::DeepModelTy>;
    fn deep_model(self) -> FSet<T::DeepModelTy> {
        panic!("DeepModel::deep_model on HashSet is specification-only")
    }
}

// --- DeepModel: BTreeMap / BTreeSet ---

/// DeepModel for `BTreeMap<K, V>` recursively applies DeepModel to keys and values.
impl<K, V> DeepModel for BTreeMap<K, V>
where
    K: DeepModel + Ord,
    K::DeepModelTy: Eq + Hash,
    V: DeepModel,
{
    type DeepModelTy = FMap<K::DeepModelTy, V::DeepModelTy>;
    fn deep_model(self) -> FMap<K::DeepModelTy, V::DeepModelTy> {
        panic!("DeepModel::deep_model on BTreeMap is specification-only")
    }
}

/// DeepModel for `BTreeSet<T>` recursively applies DeepModel to elements.
impl<T> DeepModel for BTreeSet<T>
where
    T: DeepModel + Ord,
    T::DeepModelTy: Eq + Hash,
{
    type DeepModelTy = FSet<T::DeepModelTy>;
    fn deep_model(self) -> FSet<T::DeepModelTy> {
        panic!("DeepModel::deep_model on BTreeSet is specification-only")
    }
}

// --- DeepModel: VecDeque ---

/// DeepModel for `VecDeque<T>` maps to `Seq<T::DeepModelTy>`.
///
/// Reference: Creusot `creusot-std/src/std/deque.rs`
impl<T: DeepModel> DeepModel for VecDeque<T> {
    type DeepModelTy = Seq<T::DeepModelTy>;
    fn deep_model(self) -> Seq<T::DeepModelTy> {
        panic!("DeepModel::deep_model on VecDeque<T> is specification-only")
    }
}

// --- DeepModel: Box<T> ---

/// DeepModel for `Box<T>` delegates to T's DeepModel — boxes are transparent.
///
/// Reference: Creusot `creusot-contracts/src/model.rs`
impl<T: DeepModel> DeepModel for Box<T> {
    type DeepModelTy = T::DeepModelTy;
    fn deep_model(self) -> T::DeepModelTy {
        (*self).deep_model()
    }
}

// --- DeepModel: fixed-size arrays ---

/// DeepModel for `[T; N]` maps to `Seq<T::DeepModelTy>`.
///
/// The body is specification-only because `Vec<T::DeepModelTy>` as an
/// intermediate type triggers a rustc normalization ICE when the const
/// generic `N` interacts with the associated-type projection during
/// region erasure (blocks 166/278 compat tests).
impl<T: DeepModel, const N: usize> DeepModel for [T; N] {
    type DeepModelTy = Seq<T::DeepModelTy>;
    fn deep_model(self) -> Seq<T::DeepModelTy> {
        panic!("DeepModel::deep_model on fixed-size array is specification-only")
    }
}

// --- DeepModel: logical types (identity) ---

/// DeepModel for `Seq<T>` is identity — logical sequences are already deep models.
impl<T> DeepModel for Seq<T> {
    type DeepModelTy = Seq<T>;
    fn deep_model(self) -> Seq<T> {
        self
    }
}

/// DeepModel for `FMap<K, V>` is identity — logical maps are already deep models.
impl<K, V> DeepModel for FMap<K, V> {
    type DeepModelTy = FMap<K, V>;
    fn deep_model(self) -> FMap<K, V> {
        self
    }
}

/// DeepModel for `FSet<T>` is identity — logical sets are already deep models.
impl<T> DeepModel for FSet<T> {
    type DeepModelTy = FSet<T>;
    fn deep_model(self) -> FSet<T> {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_view_i32() {
        let x: i32 = 42;
        let v = view(x);
        assert_eq!(v, Int(42));
    }

    #[test]
    fn test_view_u64() {
        let x: u64 = 1000;
        let v = view(x);
        assert_eq!(v, Int(1000));
    }

    #[test]
    fn test_view_u128() {
        // u128 within i128 range
        let x: u128 = 1000;
        let v = view(x);
        assert_eq!(v, Int(1000));
    }

    #[test]
    fn test_view_u128_at_i128_max_boundary() {
        let x = i128::MAX as u128;
        let v = view(x);
        assert_eq!(v, Int(i128::MAX));
    }

    #[test]
    #[should_panic(expected = "u128 value exceeds Int host range")]
    fn test_view_u128_panics_above_i128_max() {
        let x = i128::MAX as u128 + 1;
        let _ = view(x);
    }

    #[test]
    fn test_view_negative() {
        let x: i32 = -5;
        let v = view(x);
        assert_eq!(v, Int(-5));
    }

    #[test]
    fn test_view_vec() {
        let v = vec![1, 2, 3];
        let seq = view(v);
        assert_eq!(seq.len(), Int(3));
    }

    #[test]
    #[should_panic(expected = "View::view on shared reference is specification-only")]
    fn test_view_vec_ref() {
        let v = vec![1, 2, 3];
        let _seq = view(&v);
    }

    #[test]
    #[should_panic(expected = "View for &[T] is specification-only")]
    fn test_view_slice() {
        let arr = [1, 2, 3, 4, 5];
        let _seq = view(&arr[1..4]);
    }

    #[test]
    fn test_view_int_identity() {
        let n = Int(100);
        let v = view(n);
        assert_eq!(v, Int(100));
    }

    #[test]
    fn test_view_seq_identity() {
        let seq = Seq::from(vec![1, 2]);
        let v = view(seq);
        assert_eq!(v.len(), Int(2));
    }

    #[test]
    fn test_view_fmap_identity() {
        let fmap = FMap::empty().insert(1, 2);
        let viewed = view(fmap.clone());
        assert_eq!(viewed, fmap);
    }

    #[test]
    fn test_view_fset_identity() {
        let fset = FSet::empty().insert(1).insert(2);
        let viewed = view(fset.clone());
        assert_eq!(viewed, fset);
    }

    // --- Tests for new View implementations ---

    #[test]
    fn test_view_bool_identity() {
        assert_eq!(view(true), true);
        assert_eq!(view(false), false);
    }

    #[test]
    fn test_view_char_identity() {
        assert_eq!(view('a'), 'a');
        assert_eq!(view('\0'), '\0');
    }

    #[test]
    fn test_view_option_identity() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert_eq!(view(some), Some(42));
        assert_eq!(view(none), None);
    }

    #[test]
    fn test_view_result_identity() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("fail");
        assert_eq!(view(ok), Ok(42));
        assert_eq!(view(err), Err("fail"));
    }

    #[test]
    fn test_view_box_delegates() {
        let boxed: Box<i32> = Box::new(42);
        let v = view(boxed);
        assert_eq!(v, Int(42));
    }

    #[test]
    fn test_view_tuple_2() {
        let t = (42_i32, true);
        let v = view(t);
        assert_eq!(v, (Int(42), true));
    }

    #[test]
    fn test_view_tuple_3() {
        let t = (1_i32, 2_i32, 3_i32);
        let v = view(t);
        assert_eq!(v, (Int(1), Int(2), Int(3)));
    }

    #[test]
    #[should_panic(expected = "View::view on fixed-size array is specification-only")]
    fn test_view_fixed_array_panics() {
        let _v = view([1, 2, 3]);
    }

    // --- Tests for new DeepModel implementations ---

    #[test]
    fn test_deep_model_string() {
        let s = String::from("AB");
        let dm = s.deep_model();
        assert_eq!(dm.len(), Int(2));
    }

    #[test]
    fn test_deep_model_box() {
        let boxed: Box<i32> = Box::new(42);
        let dm = boxed.deep_model();
        assert_eq!(dm, Int(42));
    }

    #[test]
    #[should_panic(expected = "DeepModel::deep_model on fixed-size array is specification-only")]
    fn test_deep_model_array() {
        let _dm = [1_i32, 2, 3].deep_model();
    }

    #[test]
    fn test_deep_model_seq_identity() {
        let seq = Seq::from(vec![1, 2, 3]);
        let dm = seq.clone().deep_model();
        assert_eq!(dm.len(), seq.len());
    }

    #[test]
    fn test_deep_model_fmap_identity() {
        let fmap = FMap::empty().insert(1, 2);
        let dm = fmap.clone().deep_model();
        assert_eq!(dm, fmap);
    }

    #[test]
    fn test_deep_model_fset_identity() {
        let fset = FSet::empty().insert(1).insert(2);
        let dm = fset.clone().deep_model();
        assert_eq!(dm, fset);
    }

    // --- Tests for HashSet/BTreeMap/BTreeSet/VecDeque View ---

    #[test]
    fn test_view_hashset() {
        let mut hs = std::collections::HashSet::new();
        hs.insert(1);
        hs.insert(2);
        let fset = view(hs);
        assert!(fset.contains(&1));
        assert!(fset.contains(&2));
    }

    #[test]
    fn test_view_btreemap() {
        let mut bm = std::collections::BTreeMap::new();
        bm.insert(1, "a");
        bm.insert(2, "b");
        let fmap = view(bm);
        assert!(fmap.contains(&1));
        assert!(fmap.contains(&2));
    }

    #[test]
    fn test_view_btreeset() {
        let mut bs = std::collections::BTreeSet::new();
        bs.insert(10);
        bs.insert(20);
        let fset = view(bs);
        assert!(fset.contains(&10));
        assert!(fset.contains(&20));
    }

    #[test]
    fn test_view_vecdeque() {
        let mut vd = std::collections::VecDeque::new();
        vd.push_back(1);
        vd.push_back(2);
        vd.push_back(3);
        let seq = view(vd);
        assert_eq!(seq.len(), Int(3));
    }

    // --- Tests for new DeepModel implementations ---

    #[test]
    fn test_deep_model_str() {
        let s = "AB";
        let dm = s.deep_model();
        assert_eq!(dm.len(), Int(2));
    }

    #[test]
    #[should_panic(expected = "specification-only")]
    fn test_deep_model_slice() {
        let arr = [1_i32, 2, 3];
        let slice: &[i32] = &arr;
        let _dm = slice.deep_model();
    }

    #[test]
    #[should_panic(expected = "specification-only")]
    fn test_deep_model_hashmap() {
        let mut hm = std::collections::HashMap::new();
        hm.insert(1_i32, 10_i32);
        let _dm = hm.deep_model();
    }

    #[test]
    #[should_panic(expected = "specification-only")]
    fn test_deep_model_hashset() {
        let mut hs = std::collections::HashSet::new();
        hs.insert(1_i32);
        let _dm = hs.deep_model();
    }

    #[test]
    #[should_panic(expected = "specification-only")]
    fn test_deep_model_btreemap() {
        let mut bm = std::collections::BTreeMap::new();
        bm.insert(1_i32, 10_i32);
        let _dm = bm.deep_model();
    }

    #[test]
    #[should_panic(expected = "specification-only")]
    fn test_deep_model_btreeset() {
        let mut bs = std::collections::BTreeSet::new();
        bs.insert(1_i32);
        let _dm = bs.deep_model();
    }

    #[test]
    #[should_panic(expected = "specification-only")]
    fn test_deep_model_vecdeque() {
        let mut vd = std::collections::VecDeque::new();
        vd.push_back(1_i32);
        let _dm = vd.deep_model();
    }
}
