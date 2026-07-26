// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trait contract fixture for cargo-trust-wp integration tests.
//!
//! Tests Phase 1-3 of trait specification support (#357):
//! - Phase 1: Trait method contracts are discovered and inherited by impls
//! - Phase 2: Generic functions use trait contracts at call sites
//! - Phase 3: Impl contracts refine trait contracts (LSP check)

use trust_wp::*;

/// A trait with a contract on its method.
trait Counter {
    #[requires(true)]
    #[ensures(result >= 0)]
    fn count(&self) -> i32;
}

struct MyCounter {
    value: i32,
}

/// Impl that satisfies the inherited trait contract.
/// No contracts on the impl method — they should be inherited from Counter.
impl Counter for MyCounter {
    fn count(&self) -> i32 {
        42
    }
}

/// A trait with a more interesting contract.
trait Positive {
    #[ensures(result > 0)]
    fn get_positive(&self) -> i32;
}

struct AlwaysOne;

/// Impl that returns 1 — satisfies `result > 0`.
impl Positive for AlwaysOne {
    fn get_positive(&self) -> i32 {
        1
    }
}

/// Impl that violates the trait contract — returns 0, but `ensures(result > 0)`.
struct AlwaysZero;

impl Positive for AlwaysZero {
    fn get_positive(&self) -> i32 {
        0
    }
}

// =============================================================================
// Phase 2: Generic call site support
// =============================================================================

/// Generic function that calls Counter::count on any T: Counter.
/// Since Counter::count has `ensures(result >= 0)`, the postcondition
/// should be available at this call site.
///
/// This function has its own contract: `ensures(result >= 0)`.
/// Verification should succeed because Counter::count's postcondition
/// (result >= 0) satisfies this function's postcondition.
#[ensures(result >= 0)]
fn generic_count<T: Counter>(c: &T) -> i32 {
    c.count()
}

/// Generic function that calls Positive::get_positive.
/// Positive::get_positive has `ensures(result > 0)`,
/// and this function's postcondition `ensures(result > 0)` should verify.
#[ensures(result > 0)]
fn generic_positive<T: Positive>(p: &T) -> i32 {
    p.get_positive()
}

/// Generic function with a WRONG postcondition.
/// Counter::count only guarantees `result >= 0`, but this function
/// claims `result > 0`. Verification should FAIL because
/// result could be 0.
#[ensures(result > 0)]
fn generic_count_too_strong<T: Counter>(c: &T) -> i32 {
    c.count()
}

// =============================================================================
// Phase 3: Trait refinement obligations
// =============================================================================

trait RefinedCounter {
    #[requires(x >= 0)]
    #[ensures(result >= 0)]
    fn refine(&self, x: i32) -> i32;
}

/// Strengthened postcondition (`result > 0`) should refine `result >= 0`.
struct StrongerPost;

impl RefinedCounter for StrongerPost {
    #[requires(x >= 0)]
    #[ensures(result > 0)]
    fn refine(&self, x: i32) -> i32 {
        x + 1
    }
}

/// Stronger precondition (`x > 0`) should fail refinement against `x >= 0`.
struct StrongerPre;

impl RefinedCounter for StrongerPre {
    #[requires(x > 0)]
    #[ensures(result > 0)]
    fn refine(&self, x: i32) -> i32 {
        x + 1
    }
}

/// Weaker postcondition (`result >= -1`) should fail refinement vs `result >= 0`.
struct WeakerPost;

impl RefinedCounter for WeakerPost {
    #[requires(x >= 0)]
    #[ensures(result >= -1)]
    fn refine(&self, x: i32) -> i32 {
        x + 1
    }
}

// =============================================================================
// Phase 4: Generic struct field access in specifications (#717)
// =============================================================================

/// Generic struct with a field that can be accessed in contracts.
struct Wrapper<T> {
    inner: T,
}

/// Generic function accessing a field of a generic struct in a postcondition.
/// The field `inner` has type `T` which is erased to `Sort::Int` in SMT.
/// Verification should succeed because `x.inner` is returned directly.
#[ensures(result >= x.inner)]
fn get_inner_ge(x: &Wrapper<i32>) -> i32 {
    x.inner
}

/// Generic function with trait-bounded type parameter accessing struct field.
/// The Counter trait guarantees `count() >= 0`, so `result >= 0` should verify.
#[ensures(result >= 0)]
fn count_wrapper<T: Counter>(w: &Wrapper<T>) -> i32 {
    w.inner.count()
}

/// Trait refinement should treat parameter names positionally.
trait RenamedRefinement {
    #[requires(value >= 0)]
    #[ensures(result >= value)]
    fn refine_named(&self, value: i32) -> i32;
}

struct RenamedParamImpl;

/// Uses a different parameter name (`input`) than the trait (`value`).
/// Refinement should still verify after parameter-name normalization.
impl RenamedRefinement for RenamedParamImpl {
    #[requires(input >= 0)]
    #[ensures(result >= input)]
    fn refine_named(&self, input: i32) -> i32 {
        input
    }
}

// =============================================================================
// Phase 5: Trait refinement for loop-verified functions (#1652)
// =============================================================================

/// Trait with a strong postcondition that loop-verified impls must refine.
trait LoopRefinedCounter {
    #[requires(n >= 0)]
    #[ensures(result == n)]
    fn sum_n(&self, n: i32) -> i32;
}

/// Loop-verified impl with a WEAKER postcondition (`result >= 0` vs `result == n`).
///
/// The loop body satisfies the invariant and the weak postcondition, but
/// `result >= 0` does NOT imply the trait's `result == n`. Trait refinement
/// should FAIL. Before #1652, this was silently marked "verified" because
/// the loop path `continue` skipped the refinement check.
struct WeakerLoopPost;

impl LoopRefinedCounter for WeakerLoopPost {
    #[requires(n >= 0)]
    #[ensures(result >= 0)]
    #[invariant(i >= 0 && i <= n)]
    fn sum_n(&self, n: i32) -> i32 {
        let mut i = 0;
        while i < n {
            i += 1;
        }
        i
    }
}

/// Loop-verified impl with an EQUAL postcondition that refines the trait.
///
/// `result == n` is identical to the trait postcondition, so refinement should
/// pass trivially. This confirms the loop path refinement check accepts valid cases.
struct StrongerLoopPost;

impl LoopRefinedCounter for StrongerLoopPost {
    #[requires(n >= 0)]
    #[ensures(result == n)]
    #[invariant(i >= 0 && i <= n)]
    fn sum_n(&self, n: i32) -> i32 {
        let mut i = 0;
        while i < n {
            i += 1;
        }
        i
    }
}

// =============================================================================
// Phase 6: Type-invariant clause parity in trait refinement (#1579)
// =============================================================================

struct PositiveU32(u32);

impl Invariant for PositiveU32 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ > 0 }
    }
}

/// Trait whose contracts rely on invariant-provided facts.
///
/// The trait requires `true` (no constraints) and ensures `result.invariant()`.
/// An impl that takes `x: PositiveU32` and returns it should satisfy refinement
/// because the type invariant guarantees both `x.invariant()` (precondition
/// direction) and `result.invariant()` (postcondition direction).
trait InvariantRefinement {
    #[requires(true)]
    #[ensures(result.invariant())]
    fn keep(&self, x: PositiveU32) -> PositiveU32;
}

/// Positive case: refinement valid after invariant augmentation.
///
/// The impl strengthens the precondition with `x.invariant()`. Since the type
/// invariant on `PositiveU32` is always assumed for correctly-typed arguments,
/// `true => x.invariant()` holds and refinement should verify.
struct InvariantRefinementOk;

impl InvariantRefinement for InvariantRefinementOk {
    #[requires(x.invariant())]
    fn keep(&self, x: PositiveU32) -> PositiveU32 {
        x
    }
}

/// Negative case: refinement still fails when impl precondition is strictly
/// stronger than what the invariant provides.
///
/// `x.0@ > 1` is strictly stronger than `x.0@ > 0` (the invariant), so
/// `true => (x.0@ > 1)` does NOT hold — refinement must fail on the
/// precondition direction.
struct InvariantRefinementTooStrong;

impl InvariantRefinement for InvariantRefinementTooStrong {
    #[requires(x.0@ > 1)]
    fn keep(&self, x: PositiveU32) -> PositiveU32 {
        x
    }
}
