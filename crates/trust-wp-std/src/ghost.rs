// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ghost code support for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides types for ghost code - code that exists only for
//! verification purposes and is erased at compile time.
//!
//! # Ghost Code
//!
//! Ghost code enables:
//! - **Auxiliary state for proofs** - Track information needed for verification
//!   but not execution (e.g., history variables, ghost permissions)
//! - **Loop helpers** - Maintain proof-only invariant witnesses
//! - **Specification-only computation** - Express postconditions that require
//!   computing values not needed at runtime
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_wp_std::{ghost, ghost::Ghost};
//!
//! fn example() {
//!     let mut x = 0;
//!     ghost! {
//!         {
//!             let g: Ghost<i32> = Ghost::new(42);
//!             // Can use g in specifications
//!         }
//!     };
//!     x += 1; // Program code continues
//! }
//! ```
//!
//! # Design
//!
//! See `designs/2026-02-01-ghost-code.md` for the full design document.

use core::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

/// A ghost value that exists only for verification.
///
/// At runtime, `Ghost<T>` is zero-sized (`PhantomData`).
/// The verifier treats it as containing a T value.
///
/// # Properties
///
/// - Zero-sized at runtime (no memory overhead)
/// - `Copy` when `T: Copy`
/// - Cannot be dereferenced at runtime (panics)
/// - Value is available to the verifier
///
/// # Example
///
/// ```rust,no_run
/// use trust_wp_std::ghost::Ghost;
///
/// fn sum_with_ghost(n: i32) -> i32 {
///     let mut sum = 0;
///     // Ghost variable tracks partial sums for proof
///     let _ghost_partial = Ghost::new(vec![0i32]);
///     for i in 0..n {
///         sum += i;
///     }
///     sum
/// }
/// ```
#[repr(transparent)]
#[must_use]
pub struct Ghost<T: ?Sized>(PhantomData<T>);

impl<T: ?Sized> Copy for Ghost<T> {}

impl<T: ?Sized> Clone for Ghost<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Ghost<T> {
    /// Creusot-compatible ghost clone of the wrapped logical value.
    ///
    /// `Ghost<T>` is `Copy`, so the standard `Clone` impl returns another
    /// `Ghost<T>`. Creusot examples also use `ghost!(g.clone())` to clone the
    /// logical payload and then wrap it back in `Ghost<T>`. This inherent
    /// method gives method-call syntax that shape without producing
    /// `Ghost<Ghost<T>>`.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. Ghost blocks erase this path outside
    /// verification.
    #[doc(hidden)]
    pub fn clone(&self) -> T {
        panic!("Ghost::clone called at runtime - only valid in ghost code")
    }
}

/// Specification strings for ghost-related methods.
#[doc(hidden)]
pub mod specs {
    /// `Ghost::new(value)` -> `result == value`
    ///
    /// Note: In the SMT encoding, `Ghost<T>` is treated as `T`, so the result
    /// is equal to the input value.
    /// Uses `value` (not `self`) because `new` is an associated function,
    /// not a method — there is no `self` parameter in the MIR args. (#1572)
    pub const GHOST_NEW: &str = r"
        params: value
        ensures: result == value
    ";

    /// `Snapshot::capture(&value)` -> `result == value`
    ///
    /// `Snapshot<T>` is treated as `T` in SMT, so capturing yields the same value.
    /// Uses `value` (not `self`) because `capture` is an associated function,
    /// not a method — there is no `self` parameter in the MIR args. (#1572)
    pub const SNAPSHOT_CAPTURE: &str = r"
        params: value
        ensures: result == value
    ";

    /// Type-directed `snapshot!` capture dispatch tail
    /// (`SnapshotCaptureSelect::capture` / `SnapshotCaptureFallback::capture`).
    ///
    /// The SEMANTIC capture is the `snapshot_capture_select(&(expr))` call — its
    /// inline `&(expr)` argument is where the captured place is read (see
    /// `SNAPSHOT_CAPTURE`). The argument-less `.capture()` that consumes the
    /// selector merely converts it to a `Snapshot` carrying the same logical
    /// value, so it is an IDENTITY on its `self`: `result == self`. A real spec
    /// (rather than opaque-call handling) is required so no fail-closed
    /// `requires(false)` is injected into the enclosing VC. (bug/869)
    pub const SNAPSHOT_CAPTURE_DISPATCH: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Ghost::inner(self)` -> `result == self`
    pub const GHOST_INNER: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Ghost::inner_mut(self)` -> `result == self`
    pub const GHOST_INNER_MUT: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Ghost::into_inner(self)` -> `result == self`
    pub const GHOST_INTO_INNER: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Snapshot::inner(self)` -> `result == self`
    pub const SNAPSHOT_INNER: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Snapshot::into_inner(self)` -> `result == self`
    pub const SNAPSHOT_INTO_INNER: &str = r"
        params: self
        ensures: result == self
    ";

    /// `<Ghost<T> as Deref>::deref(&self)` -> `result == self`
    ///
    /// Ghost<T> is T at the logical level; deref yields the inner value.
    /// Since references are transparent in SMT, `result == self`. (#1572)
    pub const GHOST_DEREF: &str = r"
        params: self
        ensures: result == self
    ";

    /// `<Ghost<T> as DerefMut>::deref_mut(&mut self)` -> `result == self`
    ///
    /// Ghost<T> is T at the logical level; `deref_mut` yields the inner value.
    /// Since mutable references are transparent in SMT, `result == self`. (#1572)
    pub const GHOST_DEREF_MUT: &str = r"
        params: self
        ensures: result == self
    ";

    /// `<Snapshot<T> as Deref>::deref(&self)` -> `*result == self`
    ///
    /// Snapshot<T> is T at the logical level; deref yields a reference to the
    /// inner value. Since references are transparent in SMT, `result == self`.
    pub const SNAPSHOT_DEREF: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Snapshot::into_ghost(self)` -> `result == self`
    ///
    /// Both `Snapshot<T>` and `Ghost<T>` are `T` at the logical level, so
    /// conversion is identity.
    pub const SNAPSHOT_INTO_GHOST: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Snapshot::from_fn(f)` — deferred capture via closure.
    ///
    /// `Snapshot::from_fn` takes a closure that is never called at runtime.
    /// The verifier treats it as equivalent to calling the closure: the result
    /// is the closure's return value. However, since the closure body is
    /// typically opaque (it captures non-Copy values for logical reference),
    /// we use an empty spec to prevent opaque classification without
    /// overconstaining the result. The closure's logical effect is extracted
    /// separately through MIR analysis. (#2675)
    pub const SNAPSHOT_FROM_FN: &str = "";

    /// `Snapshot::new_phantom()` — ghost placeholder, no constraints.
    ///
    /// Used by the `snapshot!` macro for specification-only expressions
    /// (`such_that`, `dead`, struct literals) that cannot be evaluated at
    /// runtime. The snapshot value is irrelevant to verification; this spec
    /// prevents the call from being classified as Opaque and incrementing
    /// the `OpaqueCallTrueAssumption` unsoundness counter. (#2299)
    pub const SNAPSHOT_NEW_PHANTOM: &str = "";

    /// `Snapshot<Seq<T>>::push_back(self, x)` — transparent Seq push_back.
    ///
    /// `Snapshot<Seq<T>>` is `Seq<T>` at the logical level. This convenience
    /// method exists because `Seq::push_back` takes `self` by value but
    /// `Snapshot<Seq<T>>::Deref` returns `&Seq<T>`, so the by-value call
    /// cannot go through Deref. The spec delegates to the Seq push_back
    /// contract. Prevents opaque classification.
    pub const SNAPSHOT_SEQ_PUSH_BACK: &str = r"
        params: self, arg1
        ensures: result.len() == self.len() + 1
        ensures: result[self.len()] == arg1
        ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i] == self[i]
    ";

    /// `Snapshot<Seq<T>>::concat(self, other)` — transparent Seq concat.
    ///
    /// Same reasoning as `SNAPSHOT_SEQ_PUSH_BACK`. The spec delegates to the
    /// Seq concat contract. This is the most critical Snapshot convenience
    /// method: iterator `produces` clauses commonly use
    /// `visited.concat(next@)` where `visited` is `Snapshot<Seq<T>>`.
    pub const SNAPSHOT_SEQ_CONCAT: &str = r"
        params: self, arg1
        ensures: result.len() == self.len() + arg1.len()
        ensures: forall<i: Int> 0 <= i && i < self.len() ==> result[i] == self[i]
        ensures: forall<i: Int> 0 <= i && i < arg1.len() ==> result[self.len() + i] == arg1[i]
    ";

    /// `Snapshot<FMap<K,V>>::insert(self, k, v)` — transparent FMap insert.
    ///
    /// Same reasoning as `SNAPSHOT_SEQ_PUSH_BACK`. The spec delegates to the
    /// FMap insert (by-value/logical) contract. Prevents opaque classification.
    pub const SNAPSHOT_FMAP_INSERT: &str = r"
        params: self, arg1, arg2
        ensures: result.contains(arg1)
        ensures: result.lookup(arg1) == arg2
        ensures: forall<k2: _> k2 != arg1 ==> result.contains(k2) == self.contains(k2)
        ensures: forall<k2: _> k2 != arg1 && self.contains(k2) ==> result.lookup(k2) == self.lookup(k2)
    ";

    /// `Ghost::borrow(&self)` -> `result == self`
    ///
    /// Converts `&Ghost<T>` to `Ghost<&T>`. At the logical level, Ghost<T>
    /// is T and references are transparent, so this is identity. (#2671)
    pub const GHOST_BORROW: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Ghost::borrow_mut(&mut self)` -> `result == self`
    ///
    /// Converts `&mut Ghost<T>` to `Ghost<&mut T>`. At the logical level,
    /// Ghost<T> is T and references are transparent, so this is identity.
    /// (#2671)
    pub const GHOST_BORROW_MUT: &str = r"
        params: self
        ensures: result == self
    ";

    /// `Ghost::conjure()` — produces an unconstrained ghost value.
    ///
    /// Used by the `ghost!` macro expansion under `cfg(not(trust_wp))`:
    /// ```text
    /// if false { Ghost::new({block}) } else { Ghost::conjure() }
    /// ```
    /// The `else` branch is the runtime path. The verifier analyzes the
    /// `if false` branch, so `conjure` is typically dead code for verification.
    /// This empty spec prevents the call from being classified as Opaque and
    /// incrementing the `OpaqueCallTrueAssumption` unsoundness counter. (#2671)
    pub const GHOST_CONJURE: &str = "";

    /// `Ghost<(A, B)>::split(self)` — decompose a ghost pair.
    ///
    /// At the logical level, Ghost<T> is T. Splitting Ghost<(A, B)> into
    /// (Ghost<A>, Ghost<B>) yields the two components. Empty spec prevents
    /// the call from being classified as Opaque. The actual tuple field
    /// relationships are established by the encoder's tuple projection. (#2671)
    pub const GHOST_SPLIT: &str = "";

    /// `Perm<*const T>::from_ref(&T)` — decompose a shared reference.
    ///
    /// Returns `(*const T, Ghost<&Perm<*const T>>)`. Prevents opaque
    /// classification. The relationship between the pointer and the
    /// permission is implicit in the ghost encoding. (#1804)
    pub const PERM_FROM_REF: &str = "";

    /// `Perm<*const T>::from_mut(&mut T)` — decompose a mutable reference.
    ///
    /// Returns `(*mut T, Ghost<&mut Perm<*const T>>)`. Prevents opaque
    /// classification. (#1804)
    pub const PERM_FROM_MUT: &str = "";

    /// `Perm<*const T>::from_box(Box<T>)` — decompose a box.
    ///
    /// Returns `(*mut T, Ghost<Box<Perm<*const T>>>)`. Prevents opaque
    /// classification. (#1804)
    pub const PERM_FROM_BOX: &str = "";

    /// `Perm<*const T>::to_box(ptr, own)` — reconstruct a Box from a raw pointer.
    ///
    /// Returns `Box<T>`. Prevents opaque classification. Part of #2682.
    pub const PERM_TO_BOX: &str = "";

    /// `Resource::alloc(value)` — allocate a fresh resource.
    ///
    /// Returns `Ghost<Resource<R>>`. Prevents opaque classification.
    /// The resource identity is fresh (unique). (#2316)
    pub const RESOURCE_ALLOC: &str = "";

    /// `Resource::split(self, a, b)` — split a resource into two parts.
    ///
    /// Prevents opaque classification. The RA split semantics are too
    /// complex for the flat SMT model. (#2316)
    pub const RESOURCE_SPLIT: &str = "";

    /// `Resource::join(self, other)` — join two resources.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_JOIN: &str = "";

    /// `Resource::weaken(&mut self, target)` — weaken to a target value.
    ///
    /// Prevents opaque classification. No-op at runtime. (#2316)
    pub const RESOURCE_WEAKEN: &str = "";

    /// `Resource::core(&self)` — get the maximal idempotent sub-resource.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_CORE: &str = "";

    /// `Resource::split_off(&mut self, r, s)` — remove `r` from `self`, leaving `s`.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_SPLIT_OFF: &str = "";

    /// `Resource::split_mut(&mut self, a, b)` — split into two mutable borrows.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_SPLIT_MUT: &str = "";

    /// `Resource::join_in(&mut self, other)` — join `other` into `self`.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_JOIN_IN: &str = "";

    /// `Resource::take(&mut self)` — take the value, leaving unit.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_TAKE: &str = "";

    /// `Resource::update(&mut self, upd)` — apply a frame-preserving update.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_UPDATE: &str = "";

    /// `Resource::new_unit(id)` — create a unit resource for an identity.
    ///
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_NEW_UNIT: &str = "";

    /// `Perm::disjoint_lemma(&mut a, &b)` -> `a != b`
    ///
    /// Ghost lemma: two distinct permissions are disjoint. References are
    /// transparent in SMT, so `arg0` and `arg1` are the inner `Perm<T>` values.
    /// The postcondition is a predicate (no `result == ...`) so it is pushed
    /// as a `CALL_ASSUMPTION` for subsequent `proof_asserts`. (#1581)
    pub const PERM_DISJOINT_LEMMA: &str = "ensures: arg0 != arg1";

    /// `Perm::new(value)` -> `result.0 == *result.1`
    ///
    /// Creates a fresh allocation. Returns `(*mut T, Ghost<Box<Perm<T>>>)`.
    /// In the SMT encoding, the pointer and the permission token are the same
    /// abstract identity: `result.0 == *result.1`. Combined with
    /// `disjoint_lemma`, this lets the solver derive `p1 != p2` from
    /// `own1 != own2`. (#1581)
    pub const PERM_NEW: &str = "ensures: result.0 == *result.1";

    /// `Perm::val(&self) -> &C::Value` — ghost logical value accessor.
    ///
    /// In Creusot: `#[logic(opaque)] fn val<'a>(self) -> &'a C::Value { dead }`.
    /// Prevents opaque classification. The value is opaque at the SMT level;
    /// `perm@` (View for Perm) is defined as `*self.val()`. (#2316)
    pub const PERM_VAL: &str = "";

    /// `Perm::ward(&self) -> &C` — ghost container accessor.
    ///
    /// In Creusot: `#[logic(opaque)] fn ward<'a>(self) -> &'a C { dead }`.
    /// Prevents opaque classification. (#2316)
    pub const PERM_WARD: &str = "";

    /// `Perm::as_ref(ptr, own) -> &T` — ghost shared dereference.
    ///
    /// In Creusot: `#[ensures(*result == *own.val())]`. Prevents opaque
    /// classification without adding semantic constraints that could
    /// conflict with the flat ghost encoding model. (#2315)
    pub const PERM_AS_REF: &str = "params: ptr, own";

    /// `Perm::as_mut(ptr, own) -> &mut T` — ghost mutable dereference.
    ///
    /// In Creusot: `#[ensures(*result == *own.val())]` plus prophecy frame.
    /// Prevents opaque classification. (#2315)
    pub const PERM_AS_MUT: &str = "params: ptr, own";

    /// `Resource::val(&self) -> &R` — ghost logical value accessor.
    ///
    /// In Creusot: `#[logic(opaque)] fn val(self) -> R { dead }`.
    /// Prevents opaque classification. (#2316)
    pub const RESOURCE_VAL: &str = "";

    /// `Resource::id_ghost(&self) -> Id` — ghost identity accessor.
    ///
    /// In Creusot: `#[ensures(result == self.id())]`. Prevents opaque
    /// classification. (#2315)
    pub const RESOURCE_ID_GHOST: &str = r"
        params: self
        ensures: result == self.id()
    ";

    /// `Resource::valid_op_lemma(&mut self, &other)` — composition validity lemma.
    ///
    /// In Creusot: `#[ensures(^self == *self)]` and `#[ensures(self@.op(other@) != None)]`.
    /// The `requires` is load-bearing for SOUNDNESS: `op(self@, other@) != None`
    /// is only TRUE when the two resources can validly compose, which for an
    /// exclusive RA (Excl, where `op` is always `None`) forces the precondition
    /// `self.id() == other.id()` to be unsatisfiable — i.e. the lemma is
    /// vacuous for Excl. Asserting the `op != None` ensures UNGATED would create
    /// a global contradiction with `Excl::op == None` and false-accept
    /// everything (the 9aec447 regression). Gated, the contradiction is local to
    /// a caller that has already established `self.id() == other.id()` (e.g.
    /// excl.rs's `if x.id_ghost()==y.id_ghost()` branch), proving that branch
    /// dead. (#2315)
    ///
    /// ENCODING CONSTRAINT: the `self@.op(other@) != None` clause is UNENCODABLE
    /// (the ay encoder has no `op` method and the RA element is erased before
    /// encoding — a hard `unknown method op` error). It is handled ONLY by the
    /// Excl-gated driver strip in `mir_analysis/extract/call_spec` (which, for a
    /// `Resource<Excl<_>>::valid_op_lemma` call, drops this clause and substitutes
    /// the sound `self.id() != other.id()`). For any NON-Excl `Resource<R>` the
    /// gate does not fire, so the `op` clause is applied as-is and hard-fails to
    /// encode — which is correct for the only current fixture (an Ag should_fail
    /// test, where rejection is the expected outcome) but means a future NON-Excl
    /// `valid_op_lemma` in a should_succeed context would not encode. Generic
    /// soundness here is also CONTINGENT on `op` staying unencodable: if `op`
    /// encoding is ever added for Ag/Frac, the `requires(id==id) => op!=None`
    /// model invariant must be added in lockstep or this spec becomes unsound.
    pub const RESOURCE_VALID_OP_LEMMA: &str = r"
        params: self, other
        requires: self.id() == other.id()
        ensures: ^self == *self
        ensures: self@.op(other@) != None
    ";

    /// `Resource::join_shared(&self, &other) -> &Self` — join shared references.
    ///
    /// In Creusot: `#[requires(self.id() == other.id())]` and
    /// `#[ensures(result.id() == self.id())]` and
    /// `#[ensures(self@.incl_eq(result@) && other@.incl_eq(result@))]`.
    ///
    /// Bounded Phase 1 spec: encodes `self@ == other@` as the key consequence
    /// of the RA join semantics — two shared resources with the same identity
    /// have equal views. This is exact for the Agree RA and an
    /// over-approximation for RAs with non-trivial inclusion (e.g., Frac).
    /// Full `incl_eq` encoding deferred to RA axiom support. (#2154)
    pub const RESOURCE_JOIN_SHARED: &str = r"
        params: self, other
        ensures: self@ == other@
    ";

    /// `NonAtomicInvariant::open(self, tokens, f)` token-guarded ghost open.
    ///
    /// The full Creusot contract is higher-order and restores the protocol via
    /// the closure postcondition. This bounded Phase 1 spec keeps the token
    /// precondition and prevents the call from falling into the
    /// `OpaqueCallTrueAssumption` fallback while the remaining closure/protocol modeling
    /// work stays in #994.
    pub const NON_ATOMIC_INVARIANT_OPEN: &str = r"
        params: self, tokens, f
        requires: tokens.contains(self.namespace())
        ensures: tokens.contains(self.namespace())
    ";

    /// `AtomicInvariant::new(value, public, namespace)` — construct an atomic invariant.
    ///
    /// Returns `Ghost<AtomicInvariant<P>>`. Prevents opaque classification.
    /// The invariant protocol semantics are complex; this just prevents demotion.
    pub const ATOMIC_INVARIANT_NEW: &str = "";

    /// `AtomicInvariant::open(&self, tokens, f)` — open an atomic invariant.
    ///
    /// The full Creusot contract is higher-order and restores the protocol via
    /// the closure postcondition. This bounded spec mirrors
    /// `NonAtomicInvariant::open`: it keeps the namespace-token guard visible
    /// and preserves token availability after the open.
    pub const ATOMIC_INVARIANT_OPEN: &str = r"
        params: self, tokens, f
        requires: tokens.contains(self.namespace())
        ensures: tokens.contains(self.namespace())
    ";

    /// `AtomicInvariantSC::new(value, public, namespace)` — construct an SC atomic invariant.
    ///
    /// Returns `Ghost<AtomicInvariantSC<P>>`. Prevents opaque classification.
    pub const ATOMIC_INVARIANT_SC_NEW: &str = "";

    /// `AtomicInvariantSC::open(&self, tokens, f)` — open an SC atomic invariant.
    ///
    /// Same bounded token contract as `AtomicInvariant::open`; full
    /// higher-order protocol restoration is deferred.
    pub const ATOMIC_INVARIANT_SC_OPEN: &str = r"
        params: self, tokens, f
        requires: tokens.contains(self.namespace())
        ensures: tokens.contains(self.namespace())
    ";

    /// `Tokens::contains(&self, namespace)` — namespace membership check.
    ///
    /// Thread wrappers hand closures fresh token sets for protocol reasoning.
    /// In this bounded shim model, token sets represent all namespaces, so
    /// containment is always true.
    pub const TOKENS_CONTAINS: &str = r"
        params: self, namespace
        ensures: result == true
    ";

    /// `Tokens::new()` — get all invariant namespace tokens.
    ///
    /// Prevents opaque classification.
    pub const TOKENS_NEW: &str = "";

    /// `Tokens::reborrow(&mut self)` — reborrow a token set.
    ///
    /// Prevents opaque classification.
    pub const TOKENS_REBORROW: &str = "";

    // =========================================================================
    // Authority specs (#2316)
    // =========================================================================

    /// `Authority::alloc() -> Ghost<Self>` — allocate a fresh authority.
    ///
    /// Prevents opaque classification. The resource algebra semantics are
    /// complex; this entry just prevents demotion.
    pub const AUTHORITY_ALLOC: &str = "";

    /// `Authority::from_resource(r) -> (Self, Fragment<R>)` — create pair.
    ///
    /// Prevents opaque classification.
    pub const AUTHORITY_FROM_RESOURCE: &str = "";

    /// `Authority::update(&mut self, &mut Fragment<R>, upd)` — local update.
    ///
    /// Carries the deterministic local-update relation to the final authority
    /// and fragment states.
    pub const AUTHORITY_UPDATE: &str = r"
        params: self, frag, upd
        requires: self.id() == frag.id()
        requires: upd.premise(self@, frag@)
        ensures: self.id() == (^self).id()
        ensures: frag.id() == (^frag).id()
        ensures: (^self)@ == upd.update(self@, frag@).0
        ensures: (^frag)@ == upd.update(self@, frag@).1
    ";

    /// `Authority::add_fragment(&mut self, Snapshot<R>) -> Fragment<R>`.
    ///
    /// Prevents opaque classification.
    pub const AUTHORITY_ADD_FRAGMENT: &str = "";

    /// `Authority::frag_lemma(&self, &Fragment<R>)` — assert fragment in authority.
    ///
    /// Prevents opaque classification.
    pub const AUTHORITY_FRAG_LEMMA: &str = "";

    /// `Authority::id_ghost(&self) -> Id` — ghost identity accessor.
    ///
    /// Prevents opaque classification.
    pub const AUTHORITY_ID_GHOST: &str = "";

    // =========================================================================
    // Fragment specs (#2316)
    // =========================================================================

    /// `Fragment::new_unit(id) -> Self` — create unit fragment.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_NEW_UNIT: &str = "";

    /// `Fragment::core(&self) -> Self` — duplicate the duplicable core.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_CORE: &str = "";

    /// `Fragment::split(self, a, b) -> (Self, Self)` — split a fragment.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_SPLIT: &str = "";

    /// `Fragment::split_off(&mut self, r, s) -> Self` — remove part from self.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_SPLIT_OFF: &str = "";

    /// `Fragment::join(self, other) -> Self` — join two fragments.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_JOIN: &str = "";

    /// `Fragment::join_in(&mut self, other)` — join other into self.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_JOIN_IN: &str = "";

    /// `Fragment::weaken(&mut self, target)` — transform self into target.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_WEAKEN: &str = "";

    /// `Fragment::valid_op_lemma(&mut self, &Self)` — composition validity.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_VALID_OP_LEMMA: &str = "";

    /// `Fragment::id_ghost(&self) -> Id` — ghost identity accessor.
    ///
    /// Prevents opaque classification.
    pub const FRAGMENT_ID_GHOST: &str = "";
}

impl<T> Ghost<T> {
    /// Create a new ghost value.
    ///
    /// The value is consumed logically for verification but not stored
    /// at runtime. The resulting `Ghost<T>` is zero-sized.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use trust_wp_std::ghost::Ghost;
    ///
    /// let x = 42;
    /// let ghost_x = Ghost::new(x);
    /// // x is consumed, ghost_x is zero-sized
    /// ```
    #[inline]
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(value: T) -> Self {
        let _ = value; // Consume but don't store
        Ghost(PhantomData)
    }

    /// Conjure a ghost value out of thin air (ghost context only).
    ///
    /// In Creusot, `Ghost::conjure()` is a trusted operation that creates
    /// a ghost value with no runtime representation. The verifier assigns
    /// a logical value to the result. At runtime, returns a zero-sized
    /// `Ghost<T>`.
    ///
    /// This is used by trusted code (e.g., `PermCell::new`) to produce
    /// ghost permission tokens.
    #[inline]
    pub fn conjure() -> Self {
        Ghost(PhantomData)
    }

    /// Get the inner value (ghost context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn inner(&self) -> &T {
        panic!("Ghost::inner called at runtime - only valid in verification context")
    }

    /// Get the inner value mutably (ghost context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn inner_mut(&mut self) -> &mut T {
        panic!("Ghost::inner_mut called at runtime - only valid in verification context")
    }
}

impl<A, B> Ghost<(A, B)> {
    /// Split a ghost pair into two ghost values.
    ///
    /// In verification, this decomposes `Ghost<(A, B)>` into
    /// `(Ghost<A>, Ghost<B>)` while preserving the logical values.
    /// At runtime, both results are zero-sized.
    ///
    /// This is used by Creusot tests for ghost permission splitting.
    #[doc(hidden)]
    pub fn split(self) -> (Ghost<A>, Ghost<B>) {
        (Ghost(PhantomData), Ghost(PhantomData))
    }
}

impl<T: ?Sized> Ghost<T> {
    /// Consume and return the inner ghost value (verification context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn into_inner(self) -> T
    where
        T: Sized,
    {
        panic!("Ghost::into_inner called at runtime - only valid in verification context")
    }

    /// Convert `&Ghost<T>` into `Ghost<&T>`.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn borrow(&self) -> Ghost<&T> {
        panic!("Ghost::borrow called at runtime - only valid in verification context")
    }

    /// Convert `&mut Ghost<T>` into `Ghost<&mut T>`.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn borrow_mut(&mut self) -> Ghost<&mut T> {
        panic!("Ghost::borrow_mut called at runtime - only valid in verification context")
    }
}

impl<T> Default for Ghost<T>
where
    T: Default,
{
    fn default() -> Self {
        Ghost::new(T::default())
    }
}

impl<T: ?Sized> fmt::Debug for Ghost<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ghost").finish_non_exhaustive()
    }
}

impl<T: ?Sized> PartialEq for Ghost<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<T: ?Sized> Eq for Ghost<T> {}

impl<T: ?Sized> Hash for Ghost<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0usize.hash(state);
    }
}

impl<T: ?Sized> Deref for Ghost<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        panic!("Ghost deref called at runtime - only valid in ghost code")
    }
}

impl<T: ?Sized> DerefMut for Ghost<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        panic!("Ghost deref_mut called at runtime - only valid in ghost code")
    }
}

impl<T: ?Sized> std::borrow::Borrow<T> for Ghost<Box<T>> {
    fn borrow(&self) -> &T {
        panic!("Ghost<Box<T>>::borrow called at runtime - only valid in ghost code")
    }
}

impl<T: ?Sized> std::borrow::BorrowMut<T> for Ghost<Box<T>> {
    fn borrow_mut(&mut self) -> &mut T {
        panic!("Ghost<Box<T>>::borrow_mut called at runtime - only valid in ghost code")
    }
}

// Safety: Ghost<T> contains no actual data, so it can be sent/shared freely
unsafe impl<T: ?Sized> Send for Ghost<T> {}
unsafe impl<T: ?Sized> Sync for Ghost<T> {}

/// A snapshot of a value captured for proof purposes.
///
/// At runtime, `Snapshot<T>` is zero-sized (`PhantomData`).
/// The verifier treats it as an immutable copy of the value at capture time.
///
/// # Key Differences from `Ghost<T>`
///
/// | Property | `Ghost<T>` | `Snapshot<T>` |
/// |----------|------------|---------------|
/// | Mutable | Yes (in ghost context) | No |
/// | Copy | Always Copy | Always Copy |
/// | Use case | Auxiliary proof state | Capturing values at program points |
///
/// # Example
///
/// ```rust,no_run
/// use trust_wp_std::ghost::Snapshot;
///
/// fn sort(v: &mut Vec<i32>) {
///     // Capture the length before modification
///     let original_len = Snapshot::capture(&v.len());
///     v.push(42);
///     // In verification: *original_len == v.len() - 1
/// }
/// ```
///
/// # Design
///
/// See `designs/2026-02-01-snapshot-type.md` for the full design document.
#[repr(transparent)]
#[must_use]
pub struct Snapshot<T: ?Sized>(PhantomData<T>);

// Snapshot<T> is always Copy regardless of T (it contains no actual data)
impl<T: ?Sized> Copy for Snapshot<T> {}

impl<T: ?Sized> Clone for Snapshot<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Snapshot<T> {
    /// Capture a snapshot of a value for proof purposes.
    ///
    /// The value is captured logically for verification but the snapshot
    /// contains no runtime data. The resulting `Snapshot<T>` is zero-sized.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use trust_wp_std::ghost::Snapshot;
    ///
    /// let x = 42;
    /// let snap = Snapshot::capture(&x);
    /// // x is NOT consumed - only a logical copy is made
    /// assert_eq!(x, 42);
    /// ```
    #[inline]
    pub fn capture(_value: &T) -> Self {
        Snapshot(PhantomData)
    }

    /// Create a snapshot from a deferred closure.
    ///
    /// Matches Creusot's `Snapshot::from_fn(fn() -> T)` API.
    /// The closure is never called at runtime — the snapshot is zero-sized.
    /// This avoids moving non-Copy values into expressions that would
    /// otherwise be consumed by `Snapshot::capture(&expr)`.
    ///
    /// Used by the `snapshot!` macro to wrap expressions that reference
    /// non-Copy values (e.g., `snapshot!((atomic, data, id))`).
    #[inline]
    #[doc(hidden)]
    pub fn from_fn<F: FnOnce() -> T>(_f: F) -> Self {
        Snapshot(PhantomData)
    }

    /// Create a phantom snapshot without an input value.
    ///
    /// Used by the `snapshot!` macro for specification-only expressions
    /// (e.g., `such_that(...)`) that cannot be evaluated at runtime.
    /// The verifier extracts the logical expression from MIR patterns.
    #[inline]
    #[doc(hidden)]
    pub fn new_phantom() -> Self {
        Snapshot(PhantomData)
    }

    /// Get the captured value (verification context only).
    ///
    /// Returns `T` by value, matching Creusot's `Snapshot::inner()` signature.
    /// In Creusot, `Snapshot<T>` is a logical wrapper; `inner()` unwraps it.
    /// Since `Snapshot<T>` is always `Copy` (zero-sized phantom), returning
    /// by value is safe and avoids E0507 ("cannot move out of a shared
    /// reference") that would occur if the caller needs an owned `T`.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn inner(self) -> T {
        panic!("Snapshot::inner called at runtime - only valid in verification context")
    }

    /// Unwrap the snapshot into its inner value (Creusot compatibility).
    ///
    /// The `snapshot!` macro rewrites `*x` arguments to `x.into_inner()`.
    /// This method provides the `into_inner()` target for `Snapshot<T>`.
    ///
    /// # Safety
    ///
    /// Verification-only — unreachable at runtime.
    pub fn into_inner(self) -> T
    where
        T: Sized,
    {
        unreachable!("Snapshot::into_inner is verification-only")
    }

    /// Convert a snapshot into a ghost value.
    ///
    /// In Creusot, `into_ghost` converts a `Snapshot<T>` (logical, immutable
    /// view) into a `Ghost<T>` (ghost, ownable value) for types implementing
    /// the `Plain` trait. Since trust-wp's ghost types are all specification-only
    /// (zero-sized phantoms), this is always safe.
    ///
    /// Reference: Creusot `creusot-std/src/snapshot.rs:111-117`
    pub fn into_ghost(self) -> Ghost<T>
    where
        T: Sized,
    {
        Ghost::conjure()
    }
}

impl<T> Snapshot<crate::logic::Seq<T>> {
    /// Creusot-compatibility shim for `snapshot_seq.push_back(x)` patterns.
    ///
    /// Snapshot values carry no runtime data, so this returns a phantom
    /// sequence placeholder while preserving type-checking shape.
    #[doc(hidden)]
    pub fn push_back(self, _x: T) -> crate::logic::Seq<T> {
        crate::logic::Seq::empty()
    }

    /// Creusot-compatibility shim for `snapshot_seq.concat(other)` patterns.
    ///
    /// `Seq::concat(self, other)` takes `self` by value, but
    /// `Snapshot<Seq<T>>` derefs to `&Seq<T>`, so the by-value call
    /// fails through Deref. This convenience method bridges the gap.
    #[doc(hidden)]
    pub fn concat(self, _other: crate::logic::Seq<T>) -> crate::logic::Seq<T> {
        crate::logic::Seq::empty()
    }
}

impl<K, V> Snapshot<crate::logic::FMap<K, V>>
where
    K: std::cmp::Eq + std::hash::Hash,
{
    /// Creusot-compatibility shim for `snapshot_fmap.insert(k, v)` patterns.
    #[doc(hidden)]
    pub fn insert(self, k: K, v: V) -> crate::logic::FMap<K, V> {
        crate::logic::FMap::empty().insert(k, v)
    }
}

impl<T> Snapshot<crate::logic::FSet<T>>
where
    T: std::cmp::Eq + std::hash::Hash,
{
    /// Creusot-compatibility shim for `snapshot_fset.insert(x)` patterns.
    ///
    /// `FSet::insert` consumes `self`, so calling it through `Snapshot`'s
    /// `Deref` would move out of the dereference (forbidden when `T` is not
    /// `Copy`). The shim re-creates an empty `FSet` and performs the insert,
    /// matching the "snapshots carry no runtime data" model used by
    /// `Snapshot<Seq<_>>::push_back` and `Snapshot<FMap<_, _>>::insert`.
    #[doc(hidden)]
    pub fn insert(self, x: T) -> crate::logic::FSet<T> {
        crate::logic::FSet::empty().insert(x)
    }
}

impl<A, B> Snapshot<crate::logic::Mapping<A, B>>
where
    A: std::cmp::Eq + std::hash::Hash + Clone,
    B: Clone,
{
    /// Creusot-compatibility shim for `snapshot_mapping.set(k, v)` patterns.
    ///
    /// `Mapping::set` borrows `&self`, but call-through `Deref` may move out
    /// of the deref for downstream `*payload_snap`-style chained derefs. The
    /// shim provides an owning `set` that builds a constant mapping seeded
    /// with the inserted value (snapshot semantics keep the result purely
    /// logical), matching the placeholder behaviour used elsewhere.
    #[doc(hidden)]
    pub fn set<K, V>(self, k: K, v: V) -> crate::logic::Mapping<A, B>
    where
        K: Into<A>,
        V: Into<B>,
    {
        let v: B = v.into();
        crate::logic::Mapping::cst(v.clone()).set(k, v)
    }
}

impl<T> Deref for Snapshot<T> {
    type Target = T;

    /// Dereference the snapshot to access the captured value.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. Deref is only valid in verification
    /// context where the verifier intercepts the operation.
    fn deref(&self) -> &Self::Target {
        panic!("Snapshot deref called at runtime - only valid in specifications")
    }
}

impl<T: ?Sized> fmt::Debug for Snapshot<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Snapshot").finish_non_exhaustive()
    }
}

impl<T> Default for Snapshot<T>
where
    T: Default,
{
    fn default() -> Self {
        Snapshot(PhantomData)
    }
}

impl<T: ?Sized> PartialEq for Snapshot<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<T: ?Sized> Eq for Snapshot<T> {}

impl<T: ?Sized> Hash for Snapshot<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0usize.hash(state);
    }
}

// Safety: Snapshot<T> contains no actual data, so it can be sent/shared freely
unsafe impl<T: ?Sized> Send for Snapshot<T> {}
unsafe impl<T: ?Sized> Sync for Snapshot<T> {}

// ---------------------------------------------------------------------------
// Type-directed snapshot capture dispatch (bug/869)
//
// `snapshot! { expr }` must, under `cfg(trust_wp)`, hand the verifier a
// logical capture of `expr` WITHOUT extending any runtime borrow it names.
// For a plain value that is exactly `Snapshot::capture(&expr)`. But when
// `expr` has type `&mut T`, `Snapshot::capture(&expr)` returns
// `Snapshot<&'b mut T>` whose lifetime `'b` is the mutable borrow's own loan;
// keeping the snapshot alive then keeps the loan alive, so a second reborrow
// of the same place is rejected with E0499 where Creusot (which ghost-erases
// the capture) compiles and proves. See `bug/869`.
//
// The fix is a `&mut`-aware capture whose OUTPUT lifetime `'r` is a fresh
// region decoupled from the input borrow, so the snapshot no longer pins the
// loan. The `snapshot!` proc-macro runs before type-checking and cannot tell
// `&mut T` from a value, so selection is done with autoref-style
// specialization: `snapshot_capture_select(&expr)` pins a zero-sized selector
// to `expr`'s type, then `.capture(&expr)` resolves to the inherent method
// (for a `&mut` referent) or the trait fallback (for a value). Both are
// zero-cost, erased phantoms. The driver recognises the dispatched `capture`
// exactly like `Snapshot::capture`, reading the captured reference from the
// call's last argument. (bug/869)

/// Marker + lifetime-decoupler implemented ONLY for `&mut U`. The
/// `snapshot!` dispatch's `&mut`-aware inherent capture is gated on this
/// bound (rather than on the receiver's type *structure*) so that, when the
/// captured expression's type is still an inference variable at the call
/// site, the bound is unprovable and the trait fallback is chosen instead of
/// the inherent method poisoning inference to `&mut _`. (bug/869)
#[doc(hidden)]
pub trait SnapshotMutRefCapture {
    /// The `U` behind the `&mut U` — used so the fresh-lifetime bound is
    /// `U: 'r`, NOT `Self: 'r` (which would re-tie `'r` to the borrow's own
    /// loan and reintroduce the E0499 this whole mechanism exists to avoid).
    type Inner: ?Sized;
    /// `&'r mut U` for a fresh `'r`.
    type Fresh<'r>
    where
        Self::Inner: 'r;
}

impl<U: ?Sized> SnapshotMutRefCapture for &mut U {
    type Inner = U;
    type Fresh<'r>
        = &'r mut U
    where
        U: 'r;
}

/// Selector that pins the captured expression's type so the `snapshot!`
/// dispatch can choose the `&mut`-aware or plain capture at type-check time.
///
/// It is constructed by [`snapshot_capture_select`] from the SOLE inline
/// reborrow `&(expr)` — the same `&expr` a direct `Snapshot::capture(&expr)`
/// takes — and carries that reference's lifetime `'a` via `PhantomData<&'a T>`
/// so the borrow stays live until `.capture()` consumes the selector, exactly
/// matching the direct-capture borrow window. Zero-sized (no runtime data);
/// the reference itself is NOT stored — the driver reads the captured place
/// from the `snapshot_capture_select` call's argument, which (being an inline
/// anonymous reborrow subexpression) reborrow-cancellation collapses to the
/// captured value, so no user-named intermediate local leaks into the
/// loop-invariant / proof_assert VCs. (bug/869)
#[doc(hidden)]
pub struct SnapshotCaptureSelect<'a, T: ?Sized>(PhantomData<&'a T>);

/// Pin a [`SnapshotCaptureSelect`] to the type behind `_r` and thread `_r`'s
/// lifetime into the selector so the captured borrow lives through `.capture()`.
///
/// This is the SINGLE evaluation point of the captured reference: the
/// `snapshot!` expansion passes exactly one inline `&(expr)` here and calls the
/// argument-less `.capture()` on the result, so the `&mut`-reborrow case
/// (`snapshot!(&mut **x)`) forms the reborrow once (no E0499 from a duplicated
/// `&mut`) and every driver pipeline sees the same anonymous, collapsible
/// reborrow it already handles for `Snapshot::capture(&expr)`. (bug/869)
#[doc(hidden)]
#[inline]
pub fn snapshot_capture_select<T: ?Sized>(_r: &T) -> SnapshotCaptureSelect<'_, T> {
    SnapshotCaptureSelect(PhantomData)
}

impl<'a, T: ?Sized + SnapshotMutRefCapture> SnapshotCaptureSelect<'a, T> {
    /// `&mut`-referent capture: the returned `Snapshot<&'r mut U>` uses a
    /// FRESH lifetime `'r` decoupled from the input borrow, so snapshotting a
    /// `&mut` does not extend its loan. This is the runtime analogue of
    /// Creusot's ghost erasure — the snapshot reads the logical witness
    /// (current + prophecy of the borrow) without pinning it live. Consuming
    /// `self` releases the captured borrow; `Snapshot` is a zero-sized phantom,
    /// never executed.
    ///
    /// Selected over the fallback only when `T` is CONCRETELY a `&mut U`
    /// (`T: SnapshotMutRefCapture`); for a plain value, or a not-yet-inferred
    /// `T`, the bound fails and the fallback is used. (bug/869)
    #[doc(hidden)]
    #[inline]
    pub fn capture<'r>(self) -> Snapshot<T::Fresh<'r>>
    where
        T::Inner: 'r,
    {
        Snapshot(PhantomData)
    }
}

/// Fallback capture for the `snapshot!` dispatch: plain values route here,
/// producing exactly the same logical capture as `Snapshot::capture`. (bug/869)
#[doc(hidden)]
pub trait SnapshotCaptureFallback<T> {
    #[doc(hidden)]
    fn capture(self) -> Snapshot<T>;
}

impl<'a, T> SnapshotCaptureFallback<T> for SnapshotCaptureSelect<'a, T> {
    #[doc(hidden)]
    #[inline]
    fn capture(self) -> Snapshot<T> {
        Snapshot(PhantomData)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ghost_is_zero_sized() {
        assert_eq!(std::mem::size_of::<Ghost<i32>>(), 0);
        assert_eq!(std::mem::size_of::<Ghost<Vec<i32>>>(), 0);
        assert_eq!(std::mem::size_of::<Ghost<String>>(), 0);
    }

    #[test]
    fn test_ghost_creation() {
        let x = 42;
        let _ghost = Ghost::new(x);
        // x is consumed, ghost is zero-sized
    }

    #[test]
    fn test_ghost_copy() {
        let ghost1: Ghost<i32> = Ghost::new(42);
        let ghost2 = ghost1; // Copy
        let ghost3 = ghost1; // Still valid because Copy
        let _ = (ghost2, ghost3);
    }

    #[test]
    #[should_panic(expected = "Ghost::inner called at runtime")]
    fn test_ghost_inner_panics() {
        let ghost: Ghost<i32> = Ghost::new(42);
        let _ = ghost.inner();
    }

    #[test]
    #[should_panic(expected = "Ghost::inner_mut called at runtime")]
    fn test_ghost_inner_mut_panics() {
        let mut ghost: Ghost<i32> = Ghost::new(42);
        let _ = ghost.inner_mut();
    }

    // === Snapshot tests ===

    #[test]
    fn test_snapshot_is_zero_sized() {
        assert_eq!(std::mem::size_of::<Snapshot<i32>>(), 0);
        assert_eq!(std::mem::size_of::<Snapshot<Vec<i32>>>(), 0);
        assert_eq!(std::mem::size_of::<Snapshot<String>>(), 0);
    }

    #[test]
    fn test_snapshot_capture_does_not_consume() {
        let x = 42;
        let _snap = Snapshot::capture(&x);
        // x is NOT consumed - only a reference is taken
        assert_eq!(x, 42);
    }

    #[test]
    fn test_snapshot_always_copy() {
        // Snapshot<T> is always Copy, even when T is not
        let v = vec![1, 2, 3];
        let snap1 = Snapshot::capture(&v);
        let snap2 = snap1; // Copy
        let snap3 = snap1; // Still valid - Snapshot is Copy
        let _ = (snap2, snap3);
        // v is still valid
        assert_eq!(v.len(), 3);
    }

    #[test]
    fn test_snapshot_clone() {
        let x = 42;
        let snap1 = Snapshot::capture(&x);
        let snap2 = snap1;
        let _ = (snap1, snap2);
    }

    #[test]
    #[should_panic(expected = "Snapshot::inner called at runtime")]
    fn test_snapshot_inner_panics() {
        let x = 42;
        let snap = Snapshot::capture(&x);
        let _ = snap.inner();
    }

    #[test]
    #[should_panic(expected = "Snapshot deref called at runtime")]
    fn test_snapshot_deref_panics() {
        let x = 42;
        let snap = Snapshot::capture(&x);
        let _ = *snap; // Deref
    }

    // === Send/Sync safety tests ===
    // These are compile-time assertions that verify the unsafe impl Send/Sync
    // for Ghost<T> and Snapshot<T> are consistent with the type system.

    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}

    #[test]
    fn test_ghost_send_sync_for_non_send_type() {
        // Ghost<Rc<i32>> should be Send+Sync even though Rc<i32> is neither,
        // because Ghost contains no actual data (PhantomData only).
        assert_send::<Ghost<std::rc::Rc<i32>>>();
        assert_sync::<Ghost<std::rc::Rc<i32>>>();
    }

    #[test]
    fn test_snapshot_send_sync_for_non_send_type() {
        // Same argument: Snapshot is PhantomData-only.
        assert_send::<Snapshot<std::rc::Rc<i32>>>();
        assert_sync::<Snapshot<std::rc::Rc<i32>>>();
    }
}

// =============================================================================
// Ghost submodules (Creusot compatibility stubs)
// =============================================================================

/// Marker trait for ghost-callable function types.
///
/// In Creusot, `FnGhost` marks closures/functions that can be called in
/// ghost context (verification only, erased at runtime). This is used with
/// `#[check(ghost)]` to annotate ghost functions that take ghost closures.
///
/// Source: Creusot `creusot-std/src/ghost.rs`
pub trait FnGhost {}

// Blanket impl: all Fn types are FnGhost (ghost-callable) for compilation.
// The actual ghost checking is done by the verifier, not at compile time.
impl<T: ?Sized> FnGhost for T {}

/// Permission tokens for ghost ownership.
///
/// In Creusot, `Perm` represents a ghost ownership token that grants
/// read/write access to a `PermCell`. This module provides stub types
/// for compilation compatibility.
///
/// Source: Creusot `creusot-std/src/ghost/perm.rs`
pub mod perm {
    use std::marker::PhantomData;

    use super::Ghost;
    use crate::trusted;

    /// Marker trait for types that act as permission containers.
    ///
    /// In Creusot, `Container` is implemented by `PermCell<T>` and raw pointer
    /// types to connect the permission token (`Perm<C>`) to the logical value
    /// type it guards. The `is_disjoint` method is a ghost predicate that the
    /// verifier uses to prove two permissions do not alias.
    ///
    /// Source: Creusot `creusot-std/src/ghost/perm.rs:9-14`
    pub trait Container {
        /// The type of value guarded by this container.
        type Value: ?Sized;

        /// Ghost predicate: two containers are disjoint (non-aliasing).
        ///
        /// Ghost-only — panics at runtime.
        #[trusted]
        fn is_disjoint(
            &self,
            _self_val: &Self::Value,
            _other: &Self,
            _other_val: &Self::Value,
        ) -> bool {
            panic!("ghost code only")
        }
    }

    /// A ghost permission token for accessing a `PermCell`.
    pub struct Perm<T> {
        _marker: PhantomData<T>,
    }

    impl<T> Perm<T> {
        /// Ghost lemma: two distinct permissions are disjoint.
        ///
        /// In Creusot, this proves that two permissions pointing to different
        /// cells cannot alias. Ghost-only — panics at runtime.
        pub fn disjoint_lemma(_a: &mut Perm<T>, _b: &Perm<T>) {
            // Ghost lemma — no runtime effect
        }

        /// Get the ward (guarded cell reference) from a permission.
        ///
        /// Ghost-only — panics at runtime.
        pub fn ward(&self) -> &T {
            panic!("ghost code only")
        }

        /// Get the logical value held by this permission.
        ///
        /// In Creusot, `Perm::val()` returns a reference to the contained
        /// value for use in specifications. Ghost-only.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/perm.rs:67-69`
        pub fn val(&self) -> &T {
            panic!("ghost code only")
        }
    }

    // Creusot: `impl<C: Container<Value: Sized>> View for Perm<C>`
    // Reference: creusot-std/src/ghost/perm.rs:101-108
    //
    // In Creusot, `perm@` dereferences the permission's logical value.
    // This enables contracts like `result == perm@` on PermCell methods.
    impl<C: Container> crate::logic::View for Perm<C>
    where
        C::Value: Sized,
    {
        type ViewTy = C::Value;

        fn view(self) -> C::Value {
            panic!("ghost code only")
        }
    }

    // Creusot: `impl<T: ?Sized> Container for *const T`
    // Reference: creusot-std/src/std/ptr.rs:513-523
    //
    // Raw pointer permissions use `T` as the value type. Disjointness is
    // address-based in Creusot; we use pointer inequality as a runtime proxy.
    impl<T> Container for *const T {
        type Value = T;

        fn is_disjoint(&self, _self_val: &T, other: &Self, _other_val: &T) -> bool {
            !core::ptr::eq(*self, *other)
        }
    }

    impl<T> Perm<*const T> {
        /// Borrow the underlying value through a raw pointer permission.
        ///
        /// In Creusot, this dereferences the pointer and validates the
        /// permission. At runtime, it simply dereferences the pointer.
        /// The `Own` parameter is generic to accept both `Ghost<&Perm<...>>`
        /// and `Ghost<&Box<Perm<...>>>` (from `ghost!(&*self.perm)` patterns
        /// where Box auto-deref doesn't chain through the ghost! macro).
        ///
        /// # Safety
        ///
        /// The pointer must be valid and properly aligned.
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:559-561`
        #[allow(
            unused_variables,
            clippy::needless_lifetimes,
            clippy::needless_pass_by_value
        )]
        pub unsafe fn as_ref<'a, Own>(ptr: *const T, own: Own) -> &'a T {
            unsafe { &*ptr }
        }

        /// Mutably borrow the underlying value through a raw pointer permission.
        ///
        /// # Safety
        ///
        /// The pointer must be valid, properly aligned, and unique.
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:589-591`
        #[allow(
            unused_variables,
            clippy::needless_lifetimes,
            clippy::needless_pass_by_value
        )]
        pub unsafe fn as_mut<'a, Own>(ptr: *mut T, own: Own) -> &'a mut T {
            unsafe { &mut *ptr }
        }

        /// Decompose a shared reference into a raw pointer and a ghost permission.
        ///
        /// In Creusot, this creates a `Perm<*const T>` from a `&T`, returning
        /// `(*const T, Ghost<&Perm<*const T>>)`. The permission tracks that the
        /// pointer is valid for the lifetime of the reference.
        ///
        /// Part of #1804.
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:573-575`
        #[allow(unused_variables)]
        pub fn from_ref(r: &T) -> (*const T, Ghost<&Perm<*const T>>) {
            (std::ptr::from_ref::<T>(r), Ghost::conjure())
        }

        /// Decompose a mutable reference into a raw pointer and a ghost permission.
        ///
        /// In Creusot, this creates a `Perm<*const T>` from a `&mut T`, returning
        /// `(*mut T, Ghost<&mut Perm<*const T>>)`. The permission tracks that the
        /// pointer is valid and unique for the lifetime of the reference.
        ///
        /// Part of #1804.
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:594-596`
        #[allow(unused_variables)]
        pub fn from_mut(r: &mut T) -> (*mut T, Ghost<&mut Perm<*const T>>) {
            (std::ptr::from_mut::<T>(r), Ghost::conjure())
        }

        /// Create a ghost permission from a `Box`, consuming ownership.
        ///
        /// In Creusot, this converts a `Box<T>` into a raw pointer and a ghost
        /// permission that tracks the allocation. The caller is responsible for
        /// eventually dropping the permission to free the memory.
        ///
        /// Part of #1804.
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:553-555`
        /// Create a fresh ghost permission and an associated raw pointer for
        /// a freshly boxed value.
        ///
        /// Returns `(*mut T, Ghost<Box<Perm<*const T>>>)` matching Creusot's
        /// `Perm::<*const T>::new` signature. The runtime side allocates and
        /// leaks a `Box<T>`; the ghost side tracks pointer ownership.
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:541-546`.
        pub fn new(value: T) -> (*mut T, Ghost<Box<Perm<*const T>>>) {
            Self::from_box(Box::new(value))
        }

        #[allow(unused_variables)]
        pub fn from_box(val: Box<T>) -> (*mut T, Ghost<Box<Perm<*const T>>>) {
            (Box::into_raw(val), Ghost::conjure())
        }

        /// Reconstruct a `Box<T>` from a raw pointer and ghost permission.
        ///
        /// In Creusot, this converts a raw pointer back into a `Box<T>`,
        /// consuming the ghost permission token.
        ///
        /// # Safety
        ///
        /// The pointer must have been created by `Box::into_raw` (or
        /// `Perm::from_box`). Safety requirements are the same as
        /// [`Box::from_raw`].
        ///
        /// Reference: Creusot `creusot-std/src/std/ptr.rs:541-543`
        #[allow(unused_variables)]
        pub unsafe fn to_box(ptr: *mut T, own: Ghost<Box<Perm<*const T>>>) -> Box<T> {
            unsafe { Box::from_raw(ptr) }
        }
    }
}

/// Resource algebra ghost tokens.
///
/// In Creusot, `Resource` represents ownership of a resource algebra element.
/// This module provides types for ghost ownership tracking and resource algebra
/// protocols. Includes `Authority`/`Fragment` wrappers for the common
/// authoritative pattern.
///
/// Source: Creusot `creusot-std/src/ghost/resource.rs`
pub mod resource {
    use std::marker::PhantomData;

    use super::{Ghost, Snapshot};
    use crate::logic::ra::{
        auth::Auth,
        update::{LocalUpdate, Update},
        Id, UnitRA, RA,
    };

    /// A ghost resource algebra token.
    ///
    /// `Resource<R>` represents ownership of a resource algebra element of
    /// type `R`. Resources track identity ([`Id`]) and support algebra
    /// operations (join, split, update).
    ///
    /// Source: Creusot `creusot-std/src/ghost/resource.rs`
    pub struct Resource<R> {
        _marker: PhantomData<R>,
    }

    // Safety: Resource<R> contains no actual data (PhantomData only).
    unsafe impl<R> Send for Resource<R> {}

    #[allow(clippy::needless_pass_by_value)] // Ghost API — by-value for Creusot compatibility
    impl<R> Resource<R> {
        /// Allocate a fresh resource with the given initial value.
        pub fn alloc(_value: Snapshot<R>) -> Ghost<Self> {
            Ghost::conjure()
        }

        /// Get the identity of this resource (logic function, spec-only).
        pub fn id(&self) -> Id {
            panic!("ghost code only")
        }

        /// Get the identity of this resource (ghost only).
        pub fn id_ghost(&self) -> Id {
            panic!("ghost code only")
        }

        /// Get the RA element contained in this resource.
        pub fn val(&self) -> &R {
            panic!("ghost code only")
        }

        /// Create a unit resource for a given identifier.
        pub fn new_unit(_id: Id) -> Self
        where
            R: UnitRA,
        {
            Self {
                _marker: PhantomData,
            }
        }

        /// Get the core (maximal idempotent sub-resource).
        pub fn core(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        /// Split a resource into two parts described by `a` and `b`.
        #[allow(unused_variables)]
        pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) {
            (
                Self {
                    _marker: PhantomData,
                },
                Self {
                    _marker: PhantomData,
                },
            )
        }

        /// Split a resource into two, re-joining when mutable borrows drop.
        #[allow(unused_variables)]
        pub fn split_mut(&mut self, a: Snapshot<R>, b: Snapshot<R>) -> (&mut Self, &mut Self) {
            panic!("ghost code only")
        }

        /// Remove `r` from `self` and return it, leaving `s` in `self`.
        #[allow(unused_variables)]
        pub fn split_off(&mut self, r: Snapshot<R>, s: Snapshot<R>) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        /// Join two owned resources together.
        #[allow(unused_variables)]
        pub fn join(self, other: Self) -> Self {
            panic!("ghost code only")
        }

        /// Same as [`Self::join`], but stores the result in `self`.
        #[allow(unused_variables)]
        pub fn join_in(&mut self, other: Self) {
            panic!("ghost code only")
        }

        /// Join two shared references to the same resource.
        pub fn join_shared<'a>(&'a self, _other: &'a Self) -> &'a Self {
            panic!("ghost code only")
        }

        /// Transforms `self` into `target` (weakening).
        #[allow(unused_variables)]
        pub fn weaken(&mut self, target: Snapshot<R>) {}

        /// Lemma: the operation of two resources with the same id is valid.
        pub fn valid_op_lemma(&mut self, _other: &Self) {}
    }

    impl<R: RA> Resource<R> {
        /// Apply a frame-preserving update to this resource.
        pub fn update<U: Update<R>>(&mut self, _upd: U) -> Snapshot<U::Choice> {
            panic!("ghost code only")
        }
    }

    impl<R: UnitRA> Resource<R> {
        /// Take the resource value out, leaving a unit resource.
        pub fn take(&mut self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }
    }

    impl<R> crate::logic::View for Resource<R> {
        type ViewTy = R;

        fn view(self) -> R {
            panic!("ghost code only")
        }
    }

    // =========================================================================
    // Authority / Fragment wrappers
    // =========================================================================

    /// Wrapper around a [`Resource`] containing an authoritative value.
    ///
    /// Source: Creusot `creusot-std/src/ghost/resource/auth.rs`
    pub struct Authority<R: UnitRA>(Resource<Auth<R>>);

    /// Wrapper around a [`Resource`] containing a fragment value.
    ///
    /// See [`Authority`].
    pub struct Fragment<R: UnitRA>(pub Resource<Auth<R>>);

    impl<R: UnitRA> crate::logic::View for Authority<R> {
        type ViewTy = R;
        fn view(self) -> R {
            panic!("ghost code only")
        }
    }

    impl<R: UnitRA> crate::logic::View for Fragment<R> {
        type ViewTy = R;
        fn view(self) -> R {
            panic!("ghost code only")
        }
    }

    impl<R: UnitRA> From<Resource<Auth<R>>> for Fragment<R> {
        fn from(value: Resource<Auth<R>>) -> Self {
            Fragment(value)
        }
    }

    #[allow(clippy::needless_pass_by_value)] // Ghost API — by-value for Creusot compatibility
    impl<R: UnitRA> Authority<R> {
        /// Id of the underlying [`Resource`].
        pub fn id(&self) -> Id {
            self.0.id()
        }

        /// Get the id (ghost only).
        pub fn id_ghost(&self) -> Id {
            self.0.id_ghost()
        }

        /// Create a new, empty authority.
        #[allow(unused_variables)]
        pub fn alloc() -> Ghost<Self> {
            Ghost::conjure()
        }

        /// Create a new authority/fragment pair from a raw [`Auth`] resource.
        #[allow(unused_variables)]
        pub fn from_resource(r: Resource<Auth<R>>) -> (Self, Fragment<R>) {
            (
                Self(Resource {
                    _marker: PhantomData,
                }),
                Fragment(Resource {
                    _marker: PhantomData,
                }),
            )
        }

        /// Perform a local update on an authority/fragment pair.
        #[allow(unused_variables)]
        pub fn update<U: LocalUpdate<R>>(&mut self, frag: &mut Fragment<R>, upd: U) {
            panic!("ghost code only")
        }

        /// Add a piece to the authority and return a new fragment for it.
        #[allow(unused_variables)]
        pub fn add_fragment(&mut self, frag: Snapshot<R>) -> Fragment<R> {
            panic!("ghost code only")
        }

        /// Asserts that the fragment is contained in this authority.
        #[allow(unused_variables)]
        pub fn frag_lemma(&self, frag: &Fragment<R>) {
            self.0.join_shared(&frag.0);
        }
    }

    #[allow(clippy::needless_pass_by_value)] // Ghost API — by-value for Creusot compatibility
    impl<R: UnitRA> Fragment<R> {
        /// Id of the underlying [`Resource`].
        pub fn id(&self) -> Id {
            self.0.id()
        }

        /// Get the id (ghost only).
        pub fn id_ghost(&self) -> Id {
            self.0.id_ghost()
        }

        /// Create a fragment containing a unit resource.
        pub fn new_unit(id: Id) -> Self {
            Fragment(Resource::new_unit(id))
        }

        /// Duplicate the duplicable core of a fragment.
        pub fn core(&self) -> Self {
            Fragment(self.0.core())
        }

        /// Split a fragment into two parts.
        #[allow(unused_variables)]
        pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) {
            (
                Fragment(Resource {
                    _marker: PhantomData,
                }),
                Fragment(Resource {
                    _marker: PhantomData,
                }),
            )
        }

        /// Remove `r` from `self`, leaving `s`.
        #[allow(unused_variables)]
        pub fn split_off(&mut self, r: Snapshot<R>, s: Snapshot<R>) -> Self {
            Fragment(Resource {
                _marker: PhantomData,
            })
        }

        /// Join two owned fragments together.
        #[allow(unused_variables)]
        pub fn join(self, other: Self) -> Self {
            panic!("ghost code only")
        }

        /// Same as [`Self::join`], but stores the result in `self`.
        #[allow(unused_variables)]
        pub fn join_in(&mut self, other: Self) {
            panic!("ghost code only")
        }

        /// Transforms `self` into `target`.
        #[allow(unused_variables)]
        pub fn weaken(&mut self, target: Snapshot<R>) {}

        /// Validates the composition of `self` and `other`.
        pub fn valid_op_lemma(&mut self, other: &Self) {
            self.0.valid_op_lemma(&other.0);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::logic::ra::{Ag, Excl};

        #[test]
        fn test_resource_is_zero_sized() {
            assert_eq!(std::mem::size_of::<Resource<i32>>(), 0);
            assert_eq!(std::mem::size_of::<Resource<Ag<i32>>>(), 0);
        }

        #[test]
        fn test_resource_alloc() {
            let snap = Snapshot::capture(&Ag(42));
            let _res: Ghost<Resource<Ag<i32>>> = Resource::alloc(snap);
        }

        #[test]
        fn test_resource_split_types() {
            fn _check<R: RA>(
                r: Resource<R>,
                a: Snapshot<R>,
                b: Snapshot<R>,
            ) -> (Resource<R>, Resource<R>) {
                r.split(a, b)
            }
        }

        #[test]
        fn test_resource_new_unit() {
            let id = Id::fresh();
            let _r: Resource<Option<Ag<i32>>> = Resource::new_unit(id);
        }

        #[test]
        fn test_resource_take() {
            let id = Id::fresh();
            let mut r: Resource<Option<Ag<i32>>> = Resource::new_unit(id);
            let _taken = r.take();
        }

        #[test]
        fn test_resource_view_impl() {
            fn _check<R>()
            where
                Resource<R>: crate::logic::View<ViewTy = R>,
            {
            }
            _check::<i32>();
            _check::<Ag<i32>>();
        }

        #[test]
        fn test_resource_send() {
            fn _assert_send<T: Send>() {}
            _assert_send::<Resource<Ag<i32>>>();
            _assert_send::<Resource<Excl<i32>>>();
        }

        #[test]
        fn test_authority_alloc() {
            let _auth: Ghost<Authority<Option<Ag<i32>>>> = Authority::alloc();
        }

        #[test]
        fn test_authority_view_impl() {
            fn _check<R: UnitRA>()
            where
                Authority<R>: crate::logic::View<ViewTy = R>,
            {
            }
        }

        #[test]
        fn test_fragment_new_unit() {
            let id = Id::fresh();
            let _frag: Fragment<Option<Ag<i32>>> = Fragment::new_unit(id);
        }

        #[test]
        fn test_fragment_from_resource() {
            fn _check<R: UnitRA>(r: Resource<Auth<R>>) -> Fragment<R> {
                Fragment::from(r)
            }
        }

        #[test]
        fn test_fragment_core() {
            let id = Id::fresh();
            let frag: Fragment<Option<Ag<i32>>> = Fragment::new_unit(id);
            let _core = frag.core();
        }

        #[test]
        fn test_fragment_valid_op_lemma() {
            let id = Id::fresh();
            let mut f1: Fragment<Option<Ag<i32>>> = Fragment::new_unit(id);
            let f2: Fragment<Option<Ag<i32>>> = Fragment::new_unit(id);
            f1.valid_op_lemma(&f2);
        }
    }
}

/// Resource invariant ghost protocols.
///
/// In Creusot, invariants provide a mechanism for maintaining logical
/// properties across ghost state transitions. This module provides stub
/// types for compilation compatibility.
///
/// There are three kinds of resource invariants:
/// - [`NonAtomicInvariant`]: for thread-local ghost state transitions
/// - [`AtomicInvariant`]: for concurrent operations (release-acquire semantics)
/// - [`AtomicInvariantSC`]: for concurrent operations (sequentially-consistent)
///
/// Source: Creusot `creusot-std/src/ghost/invariant.rs`
pub mod invariant {
    use std::marker::PhantomData;

    use super::Ghost;
    use crate::{ghost::Snapshot, logic::View, trusted};

    /// Namespace identifier for resource invariants.
    ///
    /// Upstream Creusot exposes a distinct `Namespace` type. The current facade
    /// models namespaces as `usize` because `declare_namespace!` expands to a
    /// zero-sized ID function returning `usize`.
    pub type Namespace = usize;

    /// A non-atomic invariant guarding ghost state.
    ///
    /// In Creusot, `NonAtomicInvariant<P>` is parameterized by a protocol `P`
    /// that describes valid state transitions. The invariant can be opened
    /// to access its ghost state, provided a token for the correct namespace.
    #[derive(Clone, Copy)]
    pub struct NonAtomicInvariant<P> {
        _marker: PhantomData<P>,
    }

    impl<P: Protocol> NonAtomicInvariant<P> {
        /// Construct a new `NonAtomicInvariant`.
        ///
        /// Ghost-only — returns a zero-sized ghost handle at runtime.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/invariant.rs:477-481`
        #[allow(unused_variables)]
        pub fn new(
            value: Ghost<P>,
            public: Snapshot<P::Public>,
            namespace: Snapshot<Namespace>,
        ) -> Ghost<Self> {
            Ghost::conjure()
        }

        /// Get the namespace this invariant belongs to (logic function).
        ///
        /// Ghost-only — panics at runtime.
        pub fn namespace(self) -> Namespace {
            panic!("ghost code only")
        }

        /// Get the public state guarded by this invariant (logic function).
        ///
        /// Ghost-only — panics at runtime.
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Get the private protocol state stored in the invariant.
        ///
        /// Ghost-only — panics at runtime.
        pub fn into_inner(self) -> P {
            panic!("ghost code only")
        }

        /// Open the invariant to access its ghost protocol state.
        ///
        /// This associated-function form matches Creusot's primary API:
        /// `NonAtomicInvariant::open(inv.borrow(), tokens, |state| ...)`.
        ///
        /// Ghost-only — panics at runtime.
        pub fn open<'a, R>(
            _this: Ghost<&'a Self>,
            _tokens: Ghost<Tokens<'a>>,
            _f: impl FnOnce(Ghost<&'a mut P>) -> R,
        ) -> R
        where
            P: 'a,
        {
            panic!("ghost code only")
        }

        /// Open the invariant immutably.
        ///
        /// The token argument is intentionally generic for facade compatibility:
        /// upstream accepts `&Tokens`, while existing Creusot examples often
        /// arrive here through ghost-wrapper/deref rewrites.
        pub fn open_const<Toks>(&self, _tokens: Toks) -> &P {
            panic!("ghost code only")
        }
    }

    impl<P: Protocol> Ghost<NonAtomicInvariant<P>> {
        /// Get the namespace this invariant belongs to (logic function).
        ///
        /// Ghost-only — panics at runtime.
        pub fn namespace(self) -> Namespace {
            panic!("ghost code only")
        }

        /// Get the public state guarded by this invariant (logic function).
        ///
        /// Ghost-only — panics at runtime.
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Open the invariant to access its ghost protocol state.
        ///
        /// Ghost-only — panics at runtime.
        pub fn open<'a, R>(
            self,
            _tokens: Ghost<Tokens<'a>>,
            _f: impl FnOnce(Ghost<&'a mut P>) -> R,
        ) -> R
        where
            P: 'a,
        {
            panic!("ghost code only")
        }
    }

    impl<P: Protocol> View for Ghost<std::rc::Rc<NonAtomicInvariant<P>>> {
        type ViewTy = NonAtomicInvariant<P>;

        fn view(self) -> Self::ViewTy {
            panic!("ghost code only")
        }
    }

    /// Extension trait for non-atomic invariants, matching Creusot import style.
    pub trait NonAtomicInvariantExt<'a> {
        type Inner: 'a;

        fn open<R, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> R
        where
            F: FnOnce(Ghost<&'a mut Self::Inner>) -> R;
    }

    impl<'a, P: Protocol + 'a> NonAtomicInvariantExt<'a> for Ghost<NonAtomicInvariant<P>> {
        type Inner = P;

        fn open<R, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> R
        where
            F: FnOnce(Ghost<&'a mut P>) -> R,
        {
            Ghost::<NonAtomicInvariant<P>>::open(self, tokens, f)
        }
    }

    impl<'a, P: Protocol + 'a> NonAtomicInvariantExt<'a> for Ghost<&'a NonAtomicInvariant<P>> {
        type Inner = P;

        fn open<R, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> R
        where
            F: FnOnce(Ghost<&'a mut P>) -> R,
        {
            NonAtomicInvariant::open(self, tokens, f)
        }
    }

    impl<'a, T> NonAtomicInvariantExt<'a> for Ghost<&'a T>
    where
        T: core::ops::Deref + 'a,
        Ghost<&'a T::Target>: NonAtomicInvariantExt<'a>,
    {
        type Inner = <Ghost<&'a T::Target> as NonAtomicInvariantExt<'a>>::Inner;

        fn open<R, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> R
        where
            F: FnOnce(Ghost<&'a mut Self::Inner>) -> R,
        {
            Ghost::<&T::Target>::conjure().open(tokens, f)
        }
    }

    impl<'a, L> NonAtomicInvariantExt<'a> for &'a Ghost<L>
    where
        Ghost<&'a L>: NonAtomicInvariantExt<'a>,
    {
        type Inner = <Ghost<&'a L> as NonAtomicInvariantExt<'a>>::Inner;

        fn open<R, F>(self, tokens: Ghost<Tokens<'a>>, f: F) -> R
        where
            F: FnOnce(Ghost<&'a mut Self::Inner>) -> R,
        {
            let _ = self;
            Ghost::<&L>::conjure().open(tokens, f)
        }
    }

    /// A protocol describing state transitions in an invariant.
    ///
    /// Protocols define:
    /// - `Public`: the type of public state visible outside the invariant
    /// - `public`: a logic function returning the public projection of the state
    /// - `protocol`: a predicate that must hold for every valid state
    ///
    /// API mirrors Creusot's `creusot-std/src/ghost/invariant.rs::Protocol`
    /// (1-arg `protocol`, separate `public` accessor) so that downstream tests
    /// such as `tests/should_succeed/non_atomic_invariant_cellinv.rs` compile
    /// against the same trait signature as upstream.
    pub trait Protocol: Sized {
        /// The type of public state guarded by the invariant.
        type Public;

        /// The public projection of this protocol state.
        ///
        /// In Creusot this is a `#[logic]` function: it is visible to callers
        /// holding the invariant without opening it, so `open` must not change
        /// the value it returns.
        ///
        /// Ghost-only — the default body panics at runtime, matching the rest
        /// of the ghost surface in this module.
        #[trusted]
        fn public(self) -> Self::Public {
            panic!("ghost code only")
        }

        /// The protocol predicate constraining valid states.
        ///
        /// Holds on every valid state of the invariant. Must hold when the
        /// invariant is created and re-established before it is closed.
        #[trusted]
        fn protocol(self, _public: Self::Public) -> bool {
            true
        }
    }

    /// Ghost tokens witnessing invariant namespace membership.
    ///
    /// `Tokens<'a>` grants access to invariants within a particular scope.
    /// The lifetime `'a` ties the token to the scope in which invariants
    /// can be opened.
    #[derive(Clone, Copy)]
    pub struct Tokens<'a> {
        _marker: PhantomData<&'a ()>,
    }

    impl<'a> Tokens<'a> {
        /// Check if this token set contains a token for the given namespace.
        ///
        /// Bounded shim model: token sets contain every namespace.
        #[crate::logic(open)]
        pub fn contains(&self, _namespace: usize) -> bool {
            true
        }

        /// Get the tokens for all the namespaces.
        ///
        /// This is only callable once, in `main`. Ghost-only — panics at
        /// runtime.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/invariant.rs:155-161`
        pub fn new() -> Ghost<Self> {
            panic!("ghost code only")
        }

        /// Reborrow the token, allowing it to be reused later.
        ///
        /// Ghost-only — returns a new token with a shorter lifetime.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/invariant.rs:176-179`
        pub fn reborrow(&mut self) -> Tokens<'_> {
            Tokens {
                _marker: PhantomData,
            }
        }
    }

    // =========================================================================
    // AtomicInvariant — release-acquire semantics
    // =========================================================================

    /// An atomic invariant for concurrent ghost protocols.
    ///
    /// `AtomicInvariant<P>` uses release-acquire memory ordering semantics
    /// and is parameterized by a protocol `P` describing valid state
    /// transitions. The invariant can be opened to access its ghost state,
    /// provided a token for the correct namespace.
    ///
    /// Source: Creusot `creusot-std/src/ghost/invariant.rs:312-382`
    pub struct AtomicInvariant<P> {
        _marker: PhantomData<*mut P>,
    }

    // Safety: AtomicInvariant contains no actual data (PhantomData only).
    // In Creusot, `unsafe impl<T: Send> Sync for AtomicInvariant<T>`.
    unsafe impl<P: Send> Sync for AtomicInvariant<P> {}
    // Safety: Same reasoning as Sync.
    unsafe impl<P: Send> Send for AtomicInvariant<P> {}

    impl<P: Protocol> AtomicInvariant<P> {
        /// Construct a new `AtomicInvariant`.
        ///
        /// - `value`: the private protocol state
        /// - `public`: the public state observable outside the invariant
        /// - `namespace`: the namespace for token-based reentrancy prevention
        ///
        /// Ghost-only — panics at runtime.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/invariant.rs:331-340`
        #[allow(unused_variables)]
        pub fn new(
            value: Ghost<P>,
            public: Snapshot<P::Public>,
            namespace: Snapshot<usize>,
        ) -> Ghost<Self> {
            Ghost::conjure()
        }

        /// Get the namespace associated with this invariant.
        ///
        /// Ghost-only — panics at runtime.
        pub fn namespace(self) -> usize {
            panic!("ghost code only")
        }

        /// Get the public state guarded by this invariant.
        ///
        /// Ghost-only — panics at runtime.
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Get the private protocol state stored in the invariant.
        ///
        /// Ghost-only — panics at runtime.
        pub fn into_inner(self) -> P {
            panic!("ghost code only")
        }

        /// Open the invariant to access its ghost protocol state.
        ///
        /// The closure `f` receives a mutable reference to the protocol state
        /// and must restore the protocol invariant before returning.
        ///
        /// Ghost-only — panics at runtime.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/invariant.rs:371-381`
        pub fn open<A>(&self, _tokens: Tokens<'_>, _f: impl FnOnce(&mut P) -> A) -> A {
            panic!("ghost code only")
        }
    }

    impl<P: Protocol> Ghost<AtomicInvariant<P>> {
        /// Get the namespace (delegating through ghost wrapper).
        pub fn namespace(self) -> usize {
            panic!("ghost code only")
        }

        /// Get the public state (delegating through ghost wrapper).
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Open the invariant through a ghost wrapper.
        pub fn open<'a, R>(self, _tokens: Tokens<'a>, _f: impl FnOnce(&mut P) -> R) -> R
        where
            P: 'a,
        {
            panic!("ghost code only")
        }
    }

    impl<'a, P: Protocol> Ghost<&'a AtomicInvariant<P>> {
        /// Get the namespace through a borrowed ghost wrapper.
        pub fn namespace(self) -> usize {
            panic!("ghost code only")
        }

        /// Get the public state through a borrowed ghost wrapper.
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Open the borrowed invariant through a ghost wrapper.
        pub fn open<R>(self, _tokens: Tokens<'a>, _f: impl FnOnce(&mut P) -> R) -> R
        where
            P: 'a,
        {
            panic!("ghost code only")
        }
    }

    // =========================================================================
    // AtomicInvariantSC — sequentially-consistent semantics
    // =========================================================================

    /// An atomic invariant with sequentially-consistent memory ordering.
    ///
    /// `AtomicInvariantSC<P>` is identical to [`AtomicInvariant<P>`] but uses
    /// SC semantics instead of release-acquire. This provides stronger ordering
    /// guarantees at the cost of potential performance overhead.
    ///
    /// Source: Creusot `creusot-std/src/ghost/invariant.rs:246-310`
    pub struct AtomicInvariantSC<P> {
        _marker: PhantomData<*mut P>,
    }

    // Safety: AtomicInvariantSC contains no actual data (PhantomData only).
    unsafe impl<P: Send> Sync for AtomicInvariantSC<P> {}
    unsafe impl<P: Send> Send for AtomicInvariantSC<P> {}

    impl<P: Protocol> AtomicInvariantSC<P> {
        /// Construct a new `AtomicInvariantSC`.
        ///
        /// Ghost-only — panics at runtime.
        ///
        /// Reference: Creusot `creusot-std/src/ghost/invariant.rs:260-269`
        #[allow(unused_variables)]
        pub fn new(
            value: Ghost<P>,
            public: Snapshot<P::Public>,
            namespace: Snapshot<usize>,
        ) -> Ghost<Self> {
            Ghost::conjure()
        }

        /// Get the namespace associated with this invariant.
        pub fn namespace(self) -> usize {
            panic!("ghost code only")
        }

        /// Get the public state guarded by this invariant.
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Get the private protocol state stored in the invariant.
        pub fn into_inner(self) -> P {
            panic!("ghost code only")
        }

        /// Open the invariant to access its ghost protocol state.
        ///
        /// Ghost-only — panics at runtime.
        pub fn open<A>(&self, _tokens: Tokens<'_>, _f: impl FnOnce(&mut P) -> A) -> A {
            panic!("ghost code only")
        }
    }

    impl<P: Protocol> Ghost<AtomicInvariantSC<P>> {
        /// Get the namespace (delegating through ghost wrapper).
        pub fn namespace(self) -> usize {
            panic!("ghost code only")
        }

        /// Get the public state (delegating through ghost wrapper).
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Open the invariant through a ghost wrapper.
        pub fn open<'a, R>(self, _tokens: Tokens<'a>, _f: impl FnOnce(&mut P) -> R) -> R
        where
            P: 'a,
        {
            panic!("ghost code only")
        }
    }

    impl<'a, P: Protocol> Ghost<&'a AtomicInvariantSC<P>> {
        /// Get the namespace through a borrowed ghost wrapper.
        pub fn namespace(self) -> usize {
            panic!("ghost code only")
        }

        /// Get the public state through a borrowed ghost wrapper.
        pub fn public(self) -> P::Public {
            panic!("ghost code only")
        }

        /// Open the borrowed invariant through a ghost wrapper.
        pub fn open<R>(self, _tokens: Tokens<'a>, _f: impl FnOnce(&mut P) -> R) -> R
        where
            P: 'a,
        {
            panic!("ghost code only")
        }
    }

    /// Declare a namespace for invariants (compile-time only).
    ///
    /// Creates a function returning a namespace ID.
    /// Usage: `declare_namespace! { MY_NS }` creates `fn MY_NS() -> usize`.
    #[macro_export]
    macro_rules! declare_namespace {
        ($name:ident) => {
            #[allow(non_snake_case, dead_code)]
            fn $name() -> usize {
                0 // Namespace IDs are resolved by the verifier
            }
        };
    }

    pub use declare_namespace;
}
