// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Specifications for `core::ops` function traits (`Fn`, `FnMut`, `FnOnce`)
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These specifications define closure contract semantics for verification.
//! When generic code calls a closure through Fn/FnMut/FnOnce trait bounds,
//! trust-wp-driver injects these specs to model the call using the closure's
//! `precondition` and `postcondition` specification methods.
//!
//! ## Extension Traits
//!
//! Creusot defines `FnOnceExt`, `FnMutExt`, and `FnExt` extension traits
//! that add specification methods to closures. trust-wp follows the same
//! pattern: closures are modeled as uninterpreted functions with explicit
//! `precondition`/`postcondition` predicates.
//!
//! ## Phase 1: `Fn` and `FnOnce`
//!
//! Phase 1 supports `Fn::call` and `FnOnce::call_once` with contracts
//! using `precondition` and `postcondition`/`postcondition_once` methods.
//! The closure-spec methods are uninterpreted in ay — callers provide
//! their definitions through `#[requires]` and `#[ensures]` annotations.
//!
//! ## Phase 2: `FnMut` (mutable captures)
//!
//! Phase 2 adds `FnMut::call_mut` with `postcondition_mut`, a four-place
//! predicate: `postcondition_mut(self, args, ^self, result)`. The `^self`
//! parameter represents the closure's post-state (prophecy/final value of
//! the mutable borrow). For chained calls, each call produces a new
//! symbolic state:
//!   - First call: `postcondition_mut(f_0, arg1, f_1, result1)`
//!   - Second call: `postcondition_mut(f_1, arg2, f_2, result2)`
//!
//! This naturally arises from the `RustHorn` prophecy encoding that trust-wp
//! already uses for `&mut` references.
//!
//! ## Phase 4: Resolve and `fn_mut_once` law
//!
//! Phase 4 adds the `resolve` predicate and the law connecting `FnOnce` to
//! `FnMut`: when an `FnMut` closure is called through `FnOnce`, the post-state
//! must resolve (the borrow ends). This is encoded as two Skolemized SMT axioms:
//!
//! **Forward** (`FnMut` ⇒ `FnOnce`):
//! ```text
//! forall self args res_state result.
//!   postcondition_mut(self, args, res_state, result)
//!     ==> postcondition_once(self, args, result)
//! ```
//!
//! **Reverse** (`FnOnce` ⇒ `FnMut`, Skolemized):
//! ```text
//! forall self args result.
//!   postcondition_once(self, args, result)
//!     ==> postcondition_mut(self, args, witness(self, args, result), result)
//! ```
//!
//! The Skolem function `witness` replaces the existential to avoid nested
//! alternating quantifiers. The `resolve` predicate for simple types expands
//! to `x_current == x_final`.

/// Extension trait for `FnOnce`, adding specification capabilities to closures.
///
/// trust-wp follows the Creusot pattern: closures are modeled as uninterpreted
/// functions with explicit `precondition`/`postcondition` predicates. On the
/// stable surface these traits are marker-only; the nightly surface adds logic
/// method bodies.
pub trait FnOnceExt<Args> {
    type Output;
}

/// Extension trait for `FnMut`, adding specification capabilities to closures.
pub trait FnMutExt<Args>: FnOnceExt<Args> {}

/// Extension trait for `Fn`, adding specification capabilities to closures.
pub trait FnExt<Args>: FnMutExt<Args> {}

// Stable blanket impls for ordinary closures and function pointers.
// Matches upstream Creusot arity envelope: 0..=9 arguments.
impl<O, F: FnOnce() -> O> FnOnceExt<()> for F {
    type Output = O;
}
impl<O, F: FnMut() -> O> FnMutExt<()> for F {}
impl<O, F: Fn() -> O> FnExt<()> for F {}

macro_rules! impl_fn_ext {
    ( $( $tuple:tt ),+ ) => {
        impl<$($tuple),+, O, F: FnOnce($($tuple),+) -> O> FnOnceExt<($($tuple),+,)> for F {
            type Output = O;
        }
        impl<$($tuple),+, O, F: FnMut($($tuple),+) -> O> FnMutExt<($($tuple),+,)> for F {}
        impl<$($tuple),+, O, F: Fn($($tuple),+) -> O> FnExt<($($tuple),+,)> for F {}
    };
}

impl_fn_ext! { A1 }
impl_fn_ext! { A1, A2 }
impl_fn_ext! { A1, A2, A3 }
impl_fn_ext! { A1, A2, A3, A4 }
impl_fn_ext! { A1, A2, A3, A4, A5 }
impl_fn_ext! { A1, A2, A3, A4, A5, A6 }
impl_fn_ext! { A1, A2, A3, A4, A5, A6, A7 }
impl_fn_ext! { A1, A2, A3, A4, A5, A6, A7, A8 }
impl_fn_ext! { A1, A2, A3, A4, A5, A6, A7, A8, A9 }

// ── Range-helper facade ─────────────────────────────────────────────
//
// Provides logical models for range types, matching the stable surface
// in Creusot's `creusot-std/src/std/ops.rs`. These are specification-only
// constructs used by contracts and ghost code.
//
// Reference: `reference/creusot/creusot-std/src/std/ops.rs`

use core::ops::{Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use crate::logic::{DeepModel, OrdLogic};

// --- DeepModel for Bound<T> ---

impl<T: DeepModel> DeepModel for Bound<T> {
    type DeepModelTy = Bound<T::DeepModelTy>;

    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Bound::Included(b) => Bound::Included(b.deep_model()),
            Bound::Excluded(b) => Bound::Excluded(b.deep_model()),
            Bound::Unbounded => Bound::Unbounded,
        }
    }
}

// --- RangeBounds trait ---

/// Methods for the specification of [`core::ops::RangeBounds`].
///
/// Provides logical accessors for range start/end bounds, used in
/// verification contracts. Implementations return the logical view
/// of the bounds that the range represents.
pub trait RangeBounds<T: ?Sized + DeepModel<DeepModelTy: OrdLogic>>:
    core::ops::RangeBounds<T>
{
    /// Logical start bound of this range.
    fn start_bound_logic(&self) -> Bound<&T>;

    /// Logical end bound of this range.
    fn end_bound_logic(&self) -> Bound<&T>;
}

// --- Free helper functions ---

/// Membership to an interval `(Bound<T>, Bound<T>)`.
///
/// Returns `true` when `item` falls within the half-open interval
/// defined by `lo` and `hi`. Specification-only — panics at runtime.
///
/// In Creusot, this is `#[logic(open)]` using `pearlite!` (no ownership
/// rules). Here we preserve the signature shape for facade parity.
#[allow(unused_variables, clippy::needless_pass_by_value)] // Spec-only: matches Creusot API shape
pub fn between<T: OrdLogic>(lo: Bound<T>, item: T, hi: Bound<T>) -> bool {
    panic!("specification-only: between")
}

/// Comparison with a lower bound.
///
/// Returns `true` when `item` is at or above the lower bound `lo`.
/// Specification-only — panics at runtime.
#[allow(unused_variables, clippy::needless_pass_by_value)] // Spec-only: matches Creusot API shape
pub fn lower_bound<T: OrdLogic>(lo: Bound<T>, item: T) -> bool {
    panic!("specification-only: lower_bound")
}

/// Comparison with an upper bound.
///
/// Returns `true` when `item` is at or below the upper bound `hi`.
/// Specification-only — panics at runtime.
#[allow(unused_variables, clippy::needless_pass_by_value)] // Spec-only: matches Creusot API shape
pub fn upper_bound<T: OrdLogic>(item: T, hi: Bound<T>) -> bool {
    panic!("specification-only: upper_bound")
}

// --- RangeBounds stable impls ---

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeFull {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeFrom<T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeTo<T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for Range<T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeInclusive<T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        panic!("specification-only: RangeInclusive start_bound_logic")
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        panic!("specification-only: RangeInclusive end_bound_logic")
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeToInclusive<T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for (Bound<T>, Bound<T>) {
    fn start_bound_logic(&self) -> Bound<&T> {
        match self.0 {
            Bound::Included(ref start) => Bound::Included(start),
            Bound::Excluded(ref start) => Bound::Excluded(start),
            Bound::Unbounded => Bound::Unbounded,
        }
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        match self.1 {
            Bound::Included(ref end) => Bound::Included(end),
            Bound::Excluded(ref end) => Bound::Excluded(end),
            Bound::Unbounded => Bound::Unbounded,
        }
    }
}

impl<'a, T: ?Sized + 'a + DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T>
    for (Bound<&'a T>, Bound<&'a T>)
{
    fn start_bound_logic(&self) -> Bound<&T> {
        self.0
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        self.1
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeFrom<&T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeTo<&T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for Range<&T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeInclusive<&T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        panic!("specification-only: RangeInclusive<&T> start_bound_logic")
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        panic!("specification-only: RangeInclusive<&T> end_bound_logic")
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeToInclusive<&T> {
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.end)
    }
}

// --- RangeInclusiveExt trait ---

/// Logical helper trait for `RangeInclusive<Idx>`.
///
/// Provides specification-only methods to access the start, end, and emptiness
/// of an inclusive range. These methods are the logical counterparts to the
/// runtime `RangeInclusive::start()`, `end()`, and `is_empty()` methods.
///
/// Reference: `reference/creusot/creusot-std/src/std/ops.rs`
pub trait RangeInclusiveExt<Idx> {
    /// Construct a logical `RangeInclusive` from start and end values.
    fn new_log(start: Idx, end: Idx) -> Self;

    /// Logical start of this inclusive range.
    fn start_log(self) -> Idx;

    /// Logical end of this inclusive range.
    fn end_log(self) -> Idx;

    /// Logical emptiness test for this inclusive range.
    #[allow(clippy::wrong_self_convention)] // Spec-only: consumes self per Creusot convention
    fn is_empty_log(self) -> bool
    where
        Idx: DeepModel,
        Idx::DeepModelTy: OrdLogic;
}

impl<Idx> RangeInclusiveExt<Idx> for RangeInclusive<Idx> {
    fn new_log(_start: Idx, _end: Idx) -> Self {
        panic!("specification-only: RangeInclusiveExt::new_log")
    }

    fn start_log(self) -> Idx {
        panic!("specification-only: RangeInclusiveExt::start_log")
    }

    fn end_log(self) -> Idx {
        panic!("specification-only: RangeInclusiveExt::end_log")
    }

    fn is_empty_log(self) -> bool
    where
        Idx: DeepModel,
        Idx::DeepModelTy: OrdLogic,
    {
        panic!("specification-only: RangeInclusiveExt::is_empty_log")
    }
}

// --- RangeInclusive extern spec bridge ---

crate::extern_spec! {
    impl<Idx> RangeInclusive<Idx> {
        #[ensures(result.start_log() == start)]
        #[ensures(result.end_log() == end)]
        fn new(start: Idx, end: Idx) -> Self;

        #[ensures(*result == self.start_log())]
        fn start(&self) -> &Idx;

        #[ensures(*result == self.end_log())]
        fn end(&self) -> &Idx;
    }
}

crate::extern_spec! {
    impl<Idx: PartialOrd<Idx> + DeepModel> RangeInclusive<Idx>
    where Idx::DeepModelTy: OrdLogic
    {
        #[ensures(result == self.is_empty_log())]
        fn is_empty(&self) -> bool;
    }
}

// ── Closure/Deref specification strings ─────────────────────────────

/// Internal specification definitions for trust-wp-driver lookup.
#[doc(hidden)]
pub mod specs {
    /// Contract for `RangeInclusive::new(start, end)`.
    ///
    /// This mirrors the `extern_spec!` bridge above and gives the driver a
    /// hardcoded std-spec fallback when the built-in extern registry has not
    /// preloaded this constructor.
    pub const RANGE_INCLUSIVE_NEW: &str = r"
        params: start, end
        ensures: result.start_log() == start
        ensures: result.end_log() == end
    ";

    /// Contract for `Fn::call(&self, args) -> Output`
    ///
    /// The caller must establish the closure's precondition, and after the
    /// call the postcondition holds. Since `Fn` takes `&self`, the closure
    /// state does not change.
    pub const FN_CALL: &str = r"
        params: self, arg
        requires: (*self).precondition(arg)
        ensures: (*self).postcondition(arg, result)
    ";

    /// Contract for `FnOnce::call_once(self, args) -> Output`
    ///
    /// The closure is consumed. Uses `postcondition_once` which does not
    /// require tracking state change.
    pub const FN_ONCE_CALL_ONCE: &str = r"
        params: self, arg
        requires: self.precondition(arg)
        ensures: self.postcondition_once(arg, result)
    ";

    /// Contract for `FnMut::call_mut(&mut self, args) -> Output`
    ///
    /// The closure's captures may change. Uses `postcondition_mut` which
    /// takes the pre-state, args, post-state, and result.
    pub const FN_MUT_CALL_MUT: &str = r"
        params: self, arg
        requires: (*self).precondition(arg)
        ensures: (*self).postcondition_mut(arg, ^self, result)
    ";

    /// Contract for `Deref::deref(&self) -> &Self::Target`
    ///
    /// Creusot encodes trait method contracts through method-specific
    /// pre/postcondition predicates on the trait method path.
    pub const DEREF: &str = r"
        params: self
        requires: T::deref.precondition((self,))
        ensures: T::deref.postcondition((self,), result)
    ";

    /// Contract for `DerefMut::deref_mut(&mut self) -> &mut Self::Target`
    ///
    /// Mirrors `Deref::deref` with method-specific predicates.
    pub const DEREF_MUT: &str = r"
        params: self
        requires: T::deref_mut.precondition((self,))
        ensures: T::deref_mut.postcondition((self,), result)
    ";

    /// Contract for `From::from(value) -> Self`
    ///
    /// Generic From trait spec with postcondition predicate. Type-specific
    /// From impls (like String::from(&str)) override this via first-match
    /// precedence in the spec table.
    pub const FROM: &str = r"
        params: value
        ensures: T::from.postcondition((value,), result)
    ";

    /// Contract for `Into::into(self) -> T`
    ///
    /// Generic Into trait spec with postcondition predicate. The blanket impl
    /// delegates to From::from, so this mirrors the From semantics.
    pub const INTO: &str = r"
        params: self
        ensures: T::into.postcondition((self,), result)
    ";

    /// Contract for `AsRef::as_ref(&self) -> &T`
    ///
    /// Generic AsRef trait spec — cheap reference conversion.
    /// Type-specific specs (Box, Arc, Rc) override via first-match.
    pub const AS_REF_TRAIT: &str = r"
        params: self
        ensures: T::as_ref.postcondition((self,), result)
    ";

    /// Contract for `AsMut::as_mut(&mut self) -> &mut T`
    ///
    /// Generic AsMut trait spec — cheap mutable reference conversion.
    pub const AS_MUT_TRAIT: &str = r"
        params: self
        ensures: T::as_mut.postcondition((self,), result)
    ";

    /// Contract for `core::convert::identity(x) -> x`
    ///
    /// Returns its argument unchanged.
    pub const IDENTITY: &str = r"
        params: x
        ensures: result == x
    ";

    /// Contract for `TryFrom::try_from(value) -> Result<Self, Self::Error>`
    ///
    /// Generic TryFrom trait spec with postcondition predicate. Conversion
    /// may fail, returning an Err. Type-specific impls can override via
    /// first-match precedence.
    pub const TRY_FROM: &str = r"
        params: value
        ensures: T::try_from.postcondition((value,), result)
    ";

    /// Contract for `TryInto::try_into(self) -> Result<T, Self::Error>`
    ///
    /// Generic TryInto trait spec. The blanket impl delegates to TryFrom::try_from.
    pub const TRY_INTO: &str = r"
        params: self
        ensures: T::try_into.postcondition((self,), result)
    ";

    /// Contract for generic `Index::index(&self, idx) -> &Self::Output`
    ///
    /// Trait-level fallback for any type implementing Index.
    /// Type-specific specs (Vec, HashMap, slice) take precedence via
    /// first-match ordering in the spec table. (#2689)
    pub const INDEX: &str = r"
        params: self, index
        ensures: T::index.postcondition((self, index), result)
    ";

    /// Contract for generic `IndexMut::index_mut(&mut self, idx) -> &mut Self::Output`
    ///
    /// Trait-level fallback for any type implementing IndexMut.
    /// Type-specific specs (Vec, slice) take precedence via first-match. (#2689)
    pub const INDEX_MUT: &str = r"
        params: self, index
        ensures: T::index_mut.postcondition((self, index), result)
    ";

    /// Contract for `Display::fmt(&self, f) -> fmt::Result`
    ///
    /// Generic Display trait spec. Formatting is treated as infallible
    /// (returns Ok) for verification purposes.
    pub const DISPLAY_FMT: &str = r"
        params: self, f
    ";

    /// Contract for `Debug::fmt(&self, f) -> fmt::Result`
    ///
    /// Generic Debug trait spec. Formatting is treated as infallible
    /// for verification purposes.
    pub const DEBUG_FMT: &str = r"
        params: self, f
    ";

    // ── Arithmetic operator traits ─────────────────────────────────

    /// Contract for `Add::add(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `+` operator. Type-specific integer
    /// specs in `primitives_checked` take precedence via first-match.
    pub const ADD: &str = r"
        params: self, rhs
        ensures: T::add.postcondition((self, rhs), result)
    ";

    /// Contract for `Sub::sub(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `-` operator.
    pub const SUB: &str = r"
        params: self, rhs
        ensures: T::sub.postcondition((self, rhs), result)
    ";

    /// Contract for `Mul::mul(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `*` operator.
    pub const MUL: &str = r"
        params: self, rhs
        ensures: T::mul.postcondition((self, rhs), result)
    ";

    /// Contract for `Rem::rem(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `%` operator.
    pub const REM: &str = r"
        params: self, rhs
        ensures: T::rem.postcondition((self, rhs), result)
    ";

    /// Contract for `Neg::neg(self) -> Self::Output`
    ///
    /// Generic trait fallback for unary `-` operator.
    pub const NEG: &str = r"
        params: self
        ensures: T::neg.postcondition((self,), result)
    ";

    // ── Bitwise operator traits ────────────────────────────────────

    /// Contract for `BitAnd::bitand(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `&` operator.
    pub const BIT_AND: &str = r"
        params: self, rhs
        ensures: T::bitand.postcondition((self, rhs), result)
    ";

    /// Contract for `BitOr::bitor(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `|` operator.
    pub const BIT_OR: &str = r"
        params: self, rhs
        ensures: T::bitor.postcondition((self, rhs), result)
    ";

    /// Contract for `BitXor::bitxor(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `^` operator.
    pub const BIT_XOR: &str = r"
        params: self, rhs
        ensures: T::bitxor.postcondition((self, rhs), result)
    ";

    /// Contract for `Not::not(self) -> Self::Output`
    ///
    /// Generic trait fallback for `!` operator.
    pub const NOT: &str = r"
        params: self
        ensures: T::not.postcondition((self,), result)
    ";

    /// Contract for `Shl::shl(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `<<` operator.
    pub const SHL: &str = r"
        params: self, rhs
        ensures: T::shl.postcondition((self, rhs), result)
    ";

    /// Contract for `Shr::shr(self, rhs) -> Self::Output`
    ///
    /// Generic trait fallback for `>>` operator.
    pub const SHR: &str = r"
        params: self, rhs
        ensures: T::shr.postcondition((self, rhs), result)
    ";

    // ── Assignment operator traits ─────────────────────────────────

    /// Contract for `AddAssign::add_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `+=` operator.
    pub const ADD_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::add_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `SubAssign::sub_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `-=` operator.
    pub const SUB_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::sub_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `MulAssign::mul_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `*=` operator.
    pub const MUL_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::mul_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `DivAssign::div_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `/=` operator.
    pub const DIV_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::div_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `RemAssign::rem_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `%=` operator.
    pub const REM_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::rem_assign.postcondition((self, rhs), result)
    ";

    // ── Miscellaneous traits ───────────────────────────────────────

    /// Contract for `Borrow::borrow(&self) -> &T`
    ///
    /// Generic trait fallback for Borrow trait.
    pub const BORROW: &str = r"
        params: self
        ensures: T::borrow.postcondition((self,), result)
    ";

    /// Contract for `BorrowMut::borrow_mut(&mut self) -> &mut T`
    ///
    /// Generic trait fallback for BorrowMut trait.
    pub const BORROW_MUT: &str = r"
        params: self
        ensures: T::borrow_mut.postcondition((self,), result)
    ";

    /// Contract for `Drop::drop(&mut self)`
    ///
    /// Generic trait fallback for Drop. Drop has no meaningful
    /// postcondition for verification purposes.
    pub const DROP: &str = r"
        params: self
    ";

    // ── Bitwise assignment operator traits ────────────────────────

    /// Contract for `BitAndAssign::bitand_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `&=` operator.
    pub const BIT_AND_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::bitand_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `BitOrAssign::bitor_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `|=` operator.
    pub const BIT_OR_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::bitor_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `BitXorAssign::bitxor_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `^=` operator.
    pub const BIT_XOR_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::bitxor_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `ShlAssign::shl_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `<<=` operator.
    pub const SHL_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::shl_assign.postcondition((self, rhs), result)
    ";

    /// Contract for `ShrAssign::shr_assign(&mut self, rhs)`
    ///
    /// Generic trait fallback for `>>=` operator.
    pub const SHR_ASSIGN: &str = r"
        params: self, rhs
        ensures: T::shr_assign.postcondition((self, rhs), result)
    ";

    // ── Formatting traits ─────────────────────────────────────────

    /// Contract for `fmt::Write::write_str(&mut self, s: &str) -> fmt::Result`
    ///
    /// Core formatting trait method. Prevents opaque fallback when
    /// Display/Debug impls call write_str on the Formatter.
    pub const FMT_WRITE_STR: &str = r"
        params: self, s
    ";

    /// Contract for `fmt::Write::write_fmt(&mut self, args: fmt::Arguments) -> fmt::Result`
    ///
    /// Higher-level formatting method delegating to write_str.
    pub const FMT_WRITE_FMT: &str = r"
        params: self, args
    ";

    /// Contract for `fmt::Formatter::write_str`
    ///
    /// Formatter-specific write_str — prevents opaque fallback in
    /// Display/Debug implementations that use write! or write_str.
    pub const FORMATTER_WRITE_STR: &str = r"
        params: self, data
    ";

    /// Contract for `fmt::Formatter::write_fmt`
    ///
    /// Formatter-specific write_fmt — prevents opaque fallback.
    pub const FORMATTER_WRITE_FMT: &str = r"
        params: self, fmt
    ";

    // ── Generic trait fallbacks ────────────────────────────────────

    /// Contract for generic `IntoIterator::into_iter(self) -> Self::IntoIter`
    ///
    /// Trait-level fallback for any type implementing IntoIterator.
    /// Type-specific specs (Vec, HashMap, etc.) take precedence via
    /// first-match ordering. (#2689)
    pub const INTO_ITER: &str = r"
        params: self
    ";

    /// Contract for generic `Extend::extend(&mut self, iter)`
    ///
    /// Trait-level fallback for Extend. Type-specific specs
    /// (Vec, HashMap, HashSet) take precedence via first-match. (#2689)
    pub const EXTEND: &str = r"
        params: self, iter
    ";

    /// Contract for `Iterator::size_hint(&self) -> (usize, Option<usize>)`
    ///
    /// Returns a lower and optional upper bound on remaining length.
    /// Prevents opaque fallback — commonly called internally by collect.
    pub const SIZE_HINT: &str = r"
        params: self
    ";

    /// Contract for `core::ptr::drop_in_place`
    ///
    /// Called by drop glue. Has no meaningful postcondition for
    /// verification purposes.
    pub const DROP_IN_PLACE: &str = r"
        params: to_drop
    ";
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_fn_call_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FN_CALL);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("precondition"));
        assert!(spec.ensures[0].contains("postcondition"));
    }

    #[test]
    fn test_fn_once_call_once_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FN_ONCE_CALL_ONCE);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("precondition"));
        assert!(spec.ensures[0].contains("postcondition_once"));
    }

    #[test]
    fn test_fn_mut_call_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FN_MUT_CALL_MUT);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("precondition"));
        assert!(spec.ensures[0].contains("postcondition_mut"));
    }

    #[test]
    fn test_deref_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::DEREF);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("deref.precondition"));
        assert!(spec.ensures[0].contains("deref.postcondition"));
    }

    #[test]
    fn test_deref_mut_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::DEREF_MUT);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.requires[0].contains("deref_mut.precondition"));
        assert!(spec.ensures[0].contains("deref_mut.postcondition"));
    }

    #[test]
    fn test_try_from_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::TRY_FROM);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("try_from.postcondition"));
    }

    #[test]
    fn test_try_into_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::TRY_INTO);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("try_into.postcondition"));
    }
}
