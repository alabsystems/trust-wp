// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-check-only vocabulary for specification clauses.
//!
//! `trust-wp-macros` lowers every contract clause (`requires`, `ensures`,
//! `variant`, `proof_assert!`, logic function bodies) into a closure whose
//! body calls the items below, mirroring Creusot's `creusot_std::__stubs`
//! lowering (`creusot-std-proc/src/creusot/pretyping.rs`). The closure exists
//! only so rustc type-checks the clause the way Creusot's expansion makes it
//! type-check; the trust-wp driver erases it from MIR before borrow checking
//! (`callbacks::spec_typecheck`), it is emitted only under `cfg(trust_wp)`,
//! and nothing here is ever evaluated. The verifier still reads the clause
//! text from the `trust-wp:` doc markers, so these signatures carry typing
//! only — no axioms, no semantics.
//!
//! Every function body is `unreachable_stub()`: none of them can be called
//! from code that survives MIR construction.

#![allow(
    missing_docs,
    clippy::wrong_self_convention,
    clippy::should_implement_trait,
    clippy::return_self_not_must_use,
    clippy::missing_panics_doc,
    clippy::needless_pass_by_value,
    clippy::extra_unused_type_parameters
)]

use crate::logic::{
    ops::{IndexLogic, NthBitLogic},
    FMap, FSet, Int, Mapping, Seq, View, WellFounded,
};

#[cold]
fn unreachable_stub<T>() -> T {
    panic!("trust-wp specification type-check stub evaluated")
}

/// Pearlite `a == b`: both sides must have the same type (no `PartialEq`).
pub fn equal<T: ?Sized>(_: T, _: T) -> bool {
    unreachable_stub()
}

/// Pearlite `a != b`.
pub fn neq<T: ?Sized>(_: T, _: T) -> bool {
    unreachable_stub()
}

/// Pearlite `a ==> b`.
pub fn implication(_: bool, _: bool) -> bool {
    unreachable_stub()
}

/// Pearlite `forall<binders> body`; the macro emits `|binders| -> bool { body }`.
pub fn forall<F>(_: F) -> bool {
    unreachable_stub()
}

/// Pearlite `exists<binders> body`.
pub fn exists<F>(_: F) -> bool {
    unreachable_stub()
}

/// Pearlite `old(x)`, used as `*old(x)`.
pub fn old<'a, T: ?Sized>(_: T) -> &'a T {
    unreachable_stub()
}

/// Pearlite `dead`, used as `*dead()`.
pub fn dead<'a, T: ?Sized>() -> &'a T {
    unreachable_stub()
}

/// The single argument of a `Fn` contract predicate written in trust-wp's
/// FLAT spelling (`f.precondition(a)`), as the predicate's `Args` tuple.
///
/// Creusot passes the call's arguments as ONE tuple — `f.precondition((x,))`
/// — and trust-wp's driver also reads the flat `f.precondition(x)`. With a
/// single non-tuple argument the two cannot be told apart syntactically:
/// `f.precondition(a)` is Creusot's spelling when `a: A` with `A: Tuple`
/// (`should_succeed/closures/06_fn_specs.rs`, `weaken_std`) and trust-wp's
/// when `a: i32`. So that one argument is type-checked on its own and passed
/// through this function, whose result unifies with `Args` from the `Fn`
/// bound — the receiver, the method and the remaining arguments (result
/// state, result) keep their full typing. Two or more flat arguments are
/// unambiguous and are re-tupled directly.
pub fn fn_args_of<T: ?Sized, Args>(_: &T) -> Args {
    unreachable_stub()
}

/// Unsuffixed (or `int`-suffixed) integer literal in pearlite: an `Int`.
///
/// Used where the literal stands alone (a call argument, an index, a literal
/// on BOTH sides of an operator). A literal that is one operand of an
/// operator whose other operand is not a literal goes through the `*_lit`
/// functions below instead, which take the type from that other operand.
pub fn int_lit(_: u128) -> Int {
    unreachable_stub()
}

// ---------------------------------------------------------------------------
// Unsuffixed integer literal as an operand (trust-wp's dialect)
//
// Creusot types every unsuffixed pearlite literal as `Int`
// (`creusot-std-proc` `pretyping.rs`: `View::view(#lit as i128)`), so in
// Creusot `x < 100` on an `i32` is a type error and the specification has to
// say `x@ < 100`. trust-wp's own documented surface writes the machine-int
// form directly — `#[requires(x > 0)]`, `#[ensures(result == x + 1)]`,
// `#[variant(n - i)]` — and its verifier reads the clause TEXT and discharges
// exactly that obligation, so rejecting the form here would reject
// specifications trust-wp proves.
//
// The widening is confined to the LITERAL: it may denote a value of the type
// its sibling operand already has (`Int` or a machine integer), which is what
// Rust itself does with an unsuffixed literal. The sibling's type is never
// inferred FROM the literal — these functions take it as `T` and the literal
// carries no type at all — so nothing else is relaxed: `x@ == v` with `x@:
// Int` and `v: u32` is still rejected, and so is any non-integer operand.
// ---------------------------------------------------------------------------

/// A type an unsuffixed (or `int`-suffixed) pearlite integer literal may
/// denote: `Int`, or a machine integer.
#[diagnostic::on_unimplemented(
    message = "an integer literal cannot be compared with `{Self}` in logic",
    label = "`{Self}` is neither `Int` nor a machine integer"
)]
pub trait IntLitTc {}

macro_rules! impl_int_lit_tc {
    ($($t:ty),*) => { $(impl IntLitTc for $t {})* };
}
impl_int_lit_tc!(Int, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

/// Carrier for the literal's digits in the `*_lit` calls: `123u128`, or
/// `-123i128` for a negated literal. Typing only — the value is never read,
/// and the parameter exists so the literal keeps its own span inside the
/// type-check closure. Deliberately NOT generic over the integer types: a
/// carrier that could be inferred would let the literal pull a type out of
/// thin air.
pub trait IntLitRepr {}
impl IntLitRepr for u128 {}
impl IntLitRepr for i128 {}

// Keep each comparison and operand orientation as a distinct callable item.
// THIR consumers can identify the relation by DefId without reconstructing it
// from clause text. The literal carrier still contributes no type inference.
macro_rules! literal_comparison_vehicles {
    ($($right:ident, $left:ident;)*) => {$(
        #[doc = concat!("Type-check vehicle for value ", stringify!($right), " literal.")]
        pub fn $right<T: IntLitTc, L: IntLitRepr>(_: T, _: L) -> bool {
            unreachable_stub()
        }
        #[doc = concat!("Type-check vehicle for literal ", stringify!($left), " value.")]
        pub fn $left<L: IntLitRepr, T: IntLitTc>(_: L, _: T) -> bool {
            unreachable_stub()
        }
    )*};
}

literal_comparison_vehicles! {
    eq_lit, eq_lit_left;
    ne_lit, ne_lit_left;
    lt_lit, lt_lit_left;
    le_lit, le_lit_left;
    gt_lit, gt_lit_left;
    ge_lit, ge_lit_left;
}

/// `a + <literal>`. The operator trait bound is kept, so a type that has no
/// logical `+` is still refused.
pub fn add_lit<T: IntLitTc + AddTc<Output = T>, L: IntLitRepr>(_: T, _: L) -> T {
    unreachable_stub()
}

/// `<literal> + a`, retaining the original operand order.
pub fn add_lit_left<L: IntLitRepr, T: IntLitTc + AddTc<Output = T>>(_: L, _: T) -> T {
    unreachable_stub()
}

/// `a - <literal>`.
pub fn sub_lit<T: IntLitTc + SubTc<Output = T>, L: IntLitRepr>(_: T, _: L) -> T {
    unreachable_stub()
}

/// `<literal> - a`, retaining the original operand order.
pub fn sub_lit_left<L: IntLitRepr, T: IntLitTc + SubTc<Output = T>>(_: L, _: T) -> T {
    unreachable_stub()
}

/// `a * <literal>`.
pub fn mul_lit<T: IntLitTc + MulTc<Output = T>, L: IntLitRepr>(_: T, _: L) -> T {
    unreachable_stub()
}

/// `<literal> * a`, retaining the original operand order.
pub fn mul_lit_left<L: IntLitRepr, T: IntLitTc + MulTc<Output = T>>(_: L, _: T) -> T {
    unreachable_stub()
}

/// `a / <literal>`. `DivTc` holds only for `Int`, so dividing a machine
/// integer in logic stays refused (Creusot's rule).
pub fn div_lit<T: IntLitTc + DivTc<Output = T>, L: IntLitRepr>(_: T, _: L) -> T {
    unreachable_stub()
}

/// `<literal> / a`, with the same logical-division bound.
pub fn div_lit_left<L: IntLitRepr, T: IntLitTc + DivTc<Output = T>>(_: L, _: T) -> T {
    unreachable_stub()
}

/// `a % <literal>`. `RemTc` holds only for `Int`.
pub fn rem_lit<T: IntLitTc + RemTc<Output = T>, L: IntLitRepr>(_: T, _: L) -> T {
    unreachable_stub()
}

/// `<literal> % a`, with the same logical-remainder bound.
pub fn rem_lit_left<L: IntLitRepr, T: IntLitTc + RemTc<Output = T>>(_: L, _: T) -> T {
    unreachable_stub()
}

/// `#[variant(x)]`: the variant must be well-founded.
pub fn variant_check<R: WellFounded>(_: R) -> R {
    unreachable_stub()
}

/// Loop `#[invariant]`/`#[variant]` on a `for` loop: Creusot's desugaring
/// binds `iter` (the loop's `IntoIterator::into_iter` value) and `produced`
/// (`Snapshot<Seq<Item>>`) in the clause's scope; the loop pattern is not in
/// scope. The macro emits `for_loop_tc(<iter expr>, |iter, produced| -> bool
/// { clause })`.
pub fn for_loop_tc<I: IntoIterator, F>(_: I, _: F) -> bool
where
    F: FnOnce(I::IntoIter, crate::ghost::Snapshot<Seq<I::Item>>) -> bool,
{
    unreachable_stub()
}

/// Pearlite closure `|x: A| body`: a logical mapping.
///
/// Creusot binds the parameter by reference (`|x: &A|`, occurrences `*x`).
pub fn mapping_from_fn<A, B, F: FnOnce(&A) -> B>(_: F) -> Mapping<A, B> {
    unreachable_stub()
}

/// Pearlite `seq![a, b, c]`.
pub fn seq_literal<T>(_: &[T]) -> Seq<T> {
    unreachable_stub()
}

/// Pearlite `x@`, resolved with auto-deref like Creusot's `ViewStub`.
pub trait ViewTc: View {
    fn __trust_wp_tc_view(self) -> Self::ViewTy;
}

impl<T: ?Sized + View> ViewTc for T {
    fn __trust_wp_tc_view(self) -> Self::ViewTy {
        unreachable_stub()
    }
}

/// Pearlite `a[i]`, resolved with auto-deref like Creusot's `IndexLogicStub`.
#[diagnostic::on_unimplemented(
    message = "the type cannot be indexed in logic: `{Self}` by `{I}`",
    label = "`{Self}` cannot be indexed by `{I}` in logic"
)]
pub trait IndexTc<I: ?Sized>: IndexLogic<I> {
    fn __trust_wp_tc_index(self, idx: I) -> Self::Item;
}

#[diagnostic::do_not_recommend]
impl<I: ?Sized, T: ?Sized + IndexLogic<I>> IndexTc<I> for T {
    fn __trust_wp_tc_index(self, _idx: I) -> Self::Item {
        unreachable_stub()
    }
}

macro_rules! logic_binop_trait {
    ($tr:ident, $m:ident) => {
        logic_binop_trait!($tr, $m, "no implementation of this operator in logic");
    };
    ($tr:ident, $m:ident, $msg:literal) => {
        /// Logical arithmetic operator (Creusot `creusot_std::logic::ops`).
        #[diagnostic::on_unimplemented(message = $msg)]
        pub trait $tr<Rhs = Self> {
            type Output;
            fn $m(self, other: Rhs) -> Self::Output;
        }
    };
}

logic_binop_trait!(AddTc, add_tc);
logic_binop_trait!(SubTc, sub_tc);
logic_binop_trait!(MulTc, mul_tc);
// Creusot `DivLogic`/`RemLogic` diagnostics; machine integers have neither.
logic_binop_trait!(
    DivTc,
    div_tc,
    "Cannot divide primitive integers in logic: no implementation for `{Self} / {Rhs}` in logic"
);
logic_binop_trait!(
    RemTc,
    rem_tc,
    "cannot calculate the remainder of primitive integers in logic: no implementation for `{Self} % {Rhs}` in logic"
);

/// Logical negation (Creusot `NegLogic`).
pub trait NegTc {
    type Output;
    fn neg_tc(self) -> Self::Output;
}

macro_rules! impl_binop {
    ($tr:ident, $m:ident, $($t:ty),*) => {
        $(impl $tr for $t {
            type Output = Self;
            fn $m(self, _other: Self) -> Self {
                unreachable_stub()
            }
        })*
    };
}

macro_rules! impl_neg {
    ($($t:ty),*) => {
        $(impl NegTc for $t {
            type Output = Self;
            fn neg_tc(self) -> Self {
                unreachable_stub()
            }
        })*
    };
}

// Creusot: `Int` has all five operators (`creusot-std/src/logic/int.rs`);
// machine integers have add/sub/mul/neg in logic (`creusot-std/src/std/num.rs`).
impl_binop!(AddTc, add_tc, Int, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
impl_binop!(SubTc, sub_tc, Int, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
impl_binop!(MulTc, mul_tc, Int, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
impl_binop!(DivTc, div_tc, Int);
impl_binop!(RemTc, rem_tc, Int);
impl_neg!(Int, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

// Creusot indexes std containers in logic with both `Int` and `usize`
// (`creusot-std/src/std/{vec,slice,array,deque}.rs`). Typing only: the
// driver resolves `a[i]` in specifications from the clause text.
macro_rules! index_logic_container {
    ($([$($g:tt)*] $ty:ty),* $(,)?) => {
        $(
            impl<$($g)*> IndexLogic<Int> for $ty {
                type Item = T;
                fn index_logic(self, _idx: Int) -> T {
                    unreachable_stub()
                }
            }
            impl<$($g)*> IndexLogic<usize> for $ty {
                type Item = T;
                fn index_logic(self, _idx: usize) -> T {
                    unreachable_stub()
                }
            }
        )*
    };
}

index_logic_container!(
    [T] ::std::vec::Vec<T>,
    [T] [T],
    [T, const N: usize] [T; N],
    [T] ::std::collections::VecDeque<T>,
);

// Creusot `impl<A: ?Sized, B> IndexLogic<A> for Mapping<A, B>` (Item = B) and
// `impl<K, V> IndexLogic<K> for FMap<K, V>` (Item = V).
impl<A, B> IndexLogic<A> for Mapping<A, B> {
    type Item = B;
    fn index_logic(self, _idx: A) -> B {
        unreachable_stub()
    }
}

impl<K, V> IndexLogic<K> for FMap<K, V> {
    type Item = V;
    fn index_logic(self, _idx: K) -> V {
        unreachable_stub()
    }
}

// Creusot `creusot-std/src/logic/fmap.rs`: `View for fmap::Iter<K, V>
// { ViewTy = FMap<K, V> }` (the remaining map). trust-wp's `FMapIter` is that
// iterator; its loop semantics live in the driver (`is_logical_fmap_iter`).
impl<K, V> View for crate::logic::fmap::FMapIter<K, V> {
    type ViewTy = FMap<K, V>;
    fn view(self) -> FMap<K, V> {
        unreachable_stub()
    }
}

// Creusot `creusot-std/src/std/time.rs`: durations and instants view as Int.
impl View for ::core::time::Duration {
    type ViewTy = Int;
    fn view(self) -> Int {
        unreachable_stub()
    }
}

impl View for ::std::time::Instant {
    type ViewTy = Int;
    fn view(self) -> Int {
        unreachable_stub()
    }
}

// Creusot `creusot-std/src/std/sync.rs`: `View for Arc<T> { ViewTy = Box<T> }`.
impl<T> View for ::std::sync::Arc<T> {
    type ViewTy = Box<T>;
    fn view(self) -> Box<T> {
        unreachable_stub()
    }
}

// Creusot `creusot-std/src/std/num.rs`: machine integers have `nth_bit`.
macro_rules! impl_nth_bit {
    ($($t:ty),*) => {
        $(impl NthBitLogic for $t {
            fn nth_bit(self, _n: Int) -> bool {
                unreachable_stub()
            }
        })*
    };
}
impl_nth_bit!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

// ---------------------------------------------------------------------------
// Creusot's by-value logic API (`creusot-std/src/logic/{seq,fset,fmap,
// mapping,int}.rs`), in scope only inside type-check closures.
//
// trust-wp-std's runtime model exposes several of these as `&self` methods
// with `Borrow`/`Eq`/`Hash`/`Clone` bounds. Method probing tries by-value
// receivers (trait methods included) before auto-referencing, so on a logic
// VALUE receiver these by-value methods are selected and the clause is typed
// with Creusot's signature. Typing only; never evaluated.
// ---------------------------------------------------------------------------

pub trait SeqLogicTc<T>: Sized {
    /// trust-wp's spelling of `s[ix]` on a sequence view — the repo's own
    /// `#[ensures(result == v@.index(0))]` example. Same typing as
    /// `IndexLogic<Int> for Seq<T>`; `Seq`'s runtime `std::ops::Index` is
    /// not in scope inside a type-check closure.
    fn index(self, ix: Int) -> T;
    fn len(self) -> Int;
    fn is_empty(self) -> bool;
    fn get(self, ix: Int) -> Option<T>;
    fn contains(self, x: T) -> bool;
    fn index_logic_unsized<'a>(self, ix: Int) -> &'a T;
    fn removed(self, index: Int) -> Self;
}

impl<T> SeqLogicTc<T> for Seq<T> {
    fn index(self, _ix: Int) -> T {
        unreachable_stub()
    }
    fn len(self) -> Int {
        unreachable_stub()
    }
    fn is_empty(self) -> bool {
        unreachable_stub()
    }
    fn get(self, _ix: Int) -> Option<T> {
        unreachable_stub()
    }
    fn contains(self, _x: T) -> bool {
        unreachable_stub()
    }
    fn index_logic_unsized<'a>(self, _ix: Int) -> &'a T {
        unreachable_stub()
    }
    fn removed(self, _index: Int) -> Self {
        unreachable_stub()
    }
}

pub trait SeqSeqLogicTc<T> {
    fn flatten(self) -> Seq<T>;
}

impl<T> SeqSeqLogicTc<T> for Seq<Seq<T>> {
    fn flatten(self) -> Seq<T> {
        unreachable_stub()
    }
}

pub trait FSetLogicTc<T>: Sized {
    fn len(self) -> Int;
    fn is_empty(self) -> bool;
    fn contains(self, e: T) -> bool;
    fn map<U>(self, f: Mapping<T, U>) -> FSet<U>;
    fn filter(self, f: Mapping<T, bool>) -> Self;
    fn insert(self, e: T) -> Self;
    fn remove(self, e: T) -> Self;
    fn union(self, other: Self) -> Self;
    fn intersection(self, other: Self) -> Self;
    fn difference(self, other: Self) -> Self;
    fn is_subset(self, other: Self) -> bool;
    fn is_superset(self, other: Self) -> bool;
    fn disjoint(self, other: Self) -> bool;
    fn peek(self) -> T;
}

impl<T> FSetLogicTc<T> for FSet<T> {
    fn len(self) -> Int {
        unreachable_stub()
    }
    fn is_empty(self) -> bool {
        unreachable_stub()
    }
    fn contains(self, _e: T) -> bool {
        unreachable_stub()
    }
    fn map<U>(self, _f: Mapping<T, U>) -> FSet<U> {
        unreachable_stub()
    }
    fn filter(self, _f: Mapping<T, bool>) -> Self {
        unreachable_stub()
    }
    fn insert(self, _e: T) -> Self {
        unreachable_stub()
    }
    fn remove(self, _e: T) -> Self {
        unreachable_stub()
    }
    fn union(self, _other: Self) -> Self {
        unreachable_stub()
    }
    fn intersection(self, _other: Self) -> Self {
        unreachable_stub()
    }
    fn difference(self, _other: Self) -> Self {
        unreachable_stub()
    }
    fn is_subset(self, _other: Self) -> bool {
        unreachable_stub()
    }
    fn is_superset(self, _other: Self) -> bool {
        unreachable_stub()
    }
    fn disjoint(self, _other: Self) -> bool {
        unreachable_stub()
    }
    fn peek(self) -> T {
        unreachable_stub()
    }
}

pub trait FMapLogicTc<K, V>: Sized {
    fn len(self) -> Int;
    fn is_empty(self) -> bool;
    fn get(self, k: K) -> Option<V>;
    fn lookup(self, k: K) -> V;
    fn contains(self, k: K) -> bool;
    fn disjoint(self, other: Self) -> bool;
    fn subset(self, other: Self) -> bool;
    fn keys(self) -> FSet<K>;
    fn to_mapping(self) -> Mapping<K, Option<V>>;
    fn map<V2>(self, f: Mapping<(K, V), V2>) -> FMap<K, V2>;
    fn filter(self, p: Mapping<(K, V), bool>) -> Self;
    fn filter_map<V2>(self, f: Mapping<(K, V), Option<V2>>) -> FMap<K, V2>;
}

impl<K, V> FMapLogicTc<K, V> for FMap<K, V> {
    fn len(self) -> Int {
        unreachable_stub()
    }
    fn is_empty(self) -> bool {
        unreachable_stub()
    }
    fn get(self, _k: K) -> Option<V> {
        unreachable_stub()
    }
    fn lookup(self, _k: K) -> V {
        unreachable_stub()
    }
    fn contains(self, _k: K) -> bool {
        unreachable_stub()
    }
    fn disjoint(self, _other: Self) -> bool {
        unreachable_stub()
    }
    fn subset(self, _other: Self) -> bool {
        unreachable_stub()
    }
    fn keys(self) -> FSet<K> {
        unreachable_stub()
    }
    fn to_mapping(self) -> Mapping<K, Option<V>> {
        unreachable_stub()
    }
    fn map<V2>(self, _f: Mapping<(K, V), V2>) -> FMap<K, V2> {
        unreachable_stub()
    }
    fn filter(self, _p: Mapping<(K, V), bool>) -> Self {
        unreachable_stub()
    }
    fn filter_map<V2>(self, _f: Mapping<(K, V), Option<V2>>) -> FMap<K, V2> {
        unreachable_stub()
    }
}

pub trait MappingLogicTc<A, B>: Sized {
    fn get(self, a: A) -> B;
    fn set(self, a: A, b: B) -> Self;
}

impl<A, B> MappingLogicTc<A, B> for Mapping<A, B> {
    fn get(self, _a: A) -> B {
        unreachable_stub()
    }
    fn set(self, _a: A, _b: B) -> Self {
        unreachable_stub()
    }
}

pub trait IntLogicTc: Sized {
    fn pow(self, p: Int) -> Int;
    fn pow2(self) -> Int;
    fn div_euclid(self, d: Int) -> Int;
    fn rem_euclid(self, d: Int) -> Int;
}

impl IntLogicTc for Int {
    fn pow(self, _p: Int) -> Int {
        unreachable_stub()
    }
    fn pow2(self) -> Int {
        unreachable_stub()
    }
    fn div_euclid(self, _d: Int) -> Int {
        unreachable_stub()
    }
    fn rem_euclid(self, _d: Int) -> Int {
        unreachable_stub()
    }
}

/// `proof_assert!` equality: same type, or `Int` against a machine integer
/// in either order. A snapshot built with nested literals has Rust integer
/// types in trust-wp (`Int` in Creusot); an integer inference variable is
/// resolved by Rust's integer fallback. `x == 5u64` with `x: u32` is still
/// rejected (no impl).
pub trait EqPaTc<Rhs: ?Sized> {}
impl<T: ?Sized> EqPaTc<T> for T {}
macro_rules! eq_pa_int {
    ($($t:ty),*) => { $(impl EqPaTc<$t> for Int {} impl EqPaTc<Int> for $t {})* };
}
eq_pa_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub fn equal_pa<L: ?Sized + EqPaTc<R>, R: ?Sized>(_: L, _: R) -> bool {
    unreachable_stub()
}

pub fn neq_pa<L: ?Sized + EqPaTc<R>, R: ?Sized>(_: L, _: R) -> bool {
    unreachable_stub()
}

/// `proof_assert!` indexing: `IndexLogic`, plus an `Int` index into a map
/// whose keys are machine integers (see `EqPaTc`).
pub trait IndexPaTc<I: ?Sized> {
    type Item;
    fn __trust_wp_tc_index_pa(self, idx: I) -> Self::Item;
}

impl<I: ?Sized, T: ?Sized + IndexLogic<I>> IndexPaTc<I> for T {
    type Item = <T as IndexLogic<I>>::Item;
    fn __trust_wp_tc_index_pa(self, _idx: I) -> Self::Item {
        unreachable_stub()
    }
}

macro_rules! index_pa_int_keys {
    ($($t:ty),*) => {
        $(
            impl<V> IndexPaTc<Int> for FMap<$t, V> {
                type Item = V;
                fn __trust_wp_tc_index_pa(self, _idx: Int) -> V {
                    unreachable_stub()
                }
            }
            impl<B> IndexPaTc<Int> for Mapping<$t, B> {
                type Item = B;
                fn __trust_wp_tc_index_pa(self, _idx: Int) -> B {
                    unreachable_stub()
                }
            }
        )*
    };
}
index_pa_int_keys!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

/// Creusot `creusot_std::invariant::inv<T: ?Sized>(_: T) -> bool`.
pub fn inv<T: ?Sized>(_: T) -> bool {
    unreachable_stub()
}

/// The logical types that carry extensional equality, mirroring the set
/// Creusot defines `ext_eq` on.
pub trait LogicExtEq {}

impl<T> LogicExtEq for Seq<T> {}
impl<T> LogicExtEq for FSet<T> {}
impl<K, V> LogicExtEq for FMap<K, V> {}
impl<A, B> LogicExtEq for Mapping<A, B> {}

/// Creusot's `ext_eq(self, other: Self) -> bool` on every logic collection.
///
/// A METHOD, not a free function, so the receiver goes through ordinary
/// method-call autoderef the way it does in Creusot, where `ext_eq` is an
/// inherent `#[logic]` method on each collection. A snapshot is transparent in
/// pearlite — the wrapper exists only in Rust's type system and is erased in
/// the logic — so `snap.ext_eq(x)` must reach the collection's equality
/// through `Snapshot<T>: Deref<Target = T>`, and a free call derefs nothing.
///
/// The impl is deliberately NOT blanket: a blanket one would match the
/// `Snapshot` wrapper itself at autoderef step zero and the deref would never
/// happen. Keeping `Self` on both sides is what this vehicle is for — an
/// extensional equality between two different logical types stays refused.
#[diagnostic::on_unimplemented(
    message = "the type has no logical extensional equality: `{Self}`",
    label = "`{Self}` is not a logic collection"
)]
pub trait ExtEqTc: Sized {
    fn __trust_wp_tc_ext_eq(self, other: Self) -> bool;
}

#[diagnostic::do_not_recommend]
impl<T: LogicExtEq> ExtEqTc for T {
    fn __trust_wp_tc_ext_eq(self, _other: Self) -> bool {
        unreachable_stub()
    }
}

pub trait SeqRefLogicTc<T> {
    fn to_owned_seq(self) -> Seq<T>;
}

impl<T> SeqRefLogicTc<T> for Seq<&T> {
    fn to_owned_seq(self) -> Seq<T> {
        unreachable_stub()
    }
}

pub trait FSetIntLogicTc {
    fn interval(i: Int, j: Int) -> FSet<Int>;
}

impl FSetIntLogicTc for FSet<Int> {
    fn interval(_i: Int, _j: Int) -> FSet<Int> {
        unreachable_stub()
    }
}

/// Creusot `RA::op(self, other: Self) -> Option<Self>` / `incl(self, other: Self) -> bool`.
pub trait RaLogicTc: Sized {
    fn op(self, other: Self) -> Option<Self>;
    fn incl(self, other: Self) -> bool;
}

impl<R: crate::logic::RA> RaLogicTc for R {
    fn op(self, _other: Self) -> Option<Self> {
        unreachable_stub()
    }
    fn incl(self, _other: Self) -> bool {
        unreachable_stub()
    }
}

// Creusot `creusot-std/src/{snapshot,ghost}.rs`: `^` looks through
// `Snapshot<T>` and `Ghost<T>` when `T: Fin`.
impl<T: ?Sized + crate::logic::ops::Fin> crate::logic::ops::Fin for crate::ghost::Snapshot<T> {
    type Target = T::Target;
    fn fin<'a>(self) -> &'a T::Target {
        unreachable_stub()
    }
}

impl<T: ?Sized + crate::logic::ops::Fin> crate::logic::ops::Fin for crate::ghost::Ghost<T> {
    type Target = T::Target;
    fn fin<'a>(self) -> &'a T::Target {
        unreachable_stub()
    }
}
