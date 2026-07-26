// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]

//! Closure contract fixture for cargo-trust-wp integration tests.
//!
//! Tests closure contract support (#358):
//! - Phase 1: Fn closure-spec methods (precondition, postcondition) as uninterpreted predicates
//! - Phase 1.5: Non-trusted Fn closures via call-site assumption injection
//! - Phase 2: FnMut closures with postcondition_mut (four-place predicate with ^self)

use trust_wp::{ensures, requires, trusted};

// =============================================================================
// Phase 1: Fn closures with explicit contracts (trusted wrappers)
// =============================================================================

/// Apply a Fn closure to a value, with explicit closure contracts.
///
/// Marked #[trusted]: the body is not verified, but the postcondition is
/// assumed to hold. This is correct because Fn::call's semantic contract
/// guarantees that calling a closure satisfying precondition produces a
/// result satisfying postcondition.
#[trusted]
#[requires(f.precondition(x))]
#[ensures(f.postcondition(x, result))]
fn apply_fn<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    f(x)
}

/// Positive test: a simple function with standard contracts.
///
/// This is a baseline to verify the test infrastructure works
/// and that non-closure functions are unaffected.
#[requires(x > 0)]
#[ensures(result > 0)]
fn simple_positive(x: i32) -> i32 {
    x
}

// =============================================================================
// Phase 1.5: Non-trusted Fn closure verification via call-site assumptions
// =============================================================================

/// Apply a Fn closure to a value - NOT trusted.
///
/// This function has the same contracts as apply_fn but is NOT marked #[trusted].
/// The body `f(x)` compiles to a call to `Fn::call(f, (x,))`. The driver looks
/// up Fn::call's spec (`ensures: (*self).postcondition(arg, result)`), substitutes
/// the call arguments, and pushes the resulting predicate as a call-site assumption.
///
/// Verification should succeed because:
/// 1. The precondition `f.precondition(x)` satisfies Fn::call's `requires`
/// 2. Fn::call's postcondition `f.postcondition(x, result)` becomes a call-site
///    assumption, which matches the function's `ensures` clause
#[requires(f.precondition(x))]
#[ensures(f.postcondition(x, result))]
fn verified_closure_call<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    f(x)
}

/// Same call as `verified_closure_call`, but with explicit singleton tuple
/// syntax in contracts to match `Fn::call` lowering.
#[requires(f.precondition((x,)))]
#[ensures(f.postcondition((x,), result))]
fn verified_closure_call_tuple_contract<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    f(x)
}

/// Multi-argument closure contract with explicit two-item tuple syntax.
///
/// `Fn(i32, i32)` lowers through a tuple argument in MIR. The verifier must
/// preserve tuple structure consistently between user contracts and call-site
/// substitutions.
#[requires(f.precondition((x, y)))]
#[ensures(f.postcondition((x, y), result))]
fn verified_closure_call_tuple_pair_contract<F: Fn(i32, i32) -> i32>(f: &F, x: i32, y: i32) -> i32 {
    f(x, y)
}

/// Soundness regression test: calling a closure without establishing precondition.
///
/// This used to verify unsoundly when the call-site injected only postconditions.
/// After #478, verification must fail because `f.precondition(x)` is not proven.
#[requires(true)]
#[ensures(f.postcondition(x, result))]
fn missing_call_precondition<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    f(x)
}

/// Negative test: this function's postcondition is too strong.
///
/// We only require x > 0 but claim result > x, which fails because
/// the body returns x (and x > x is false).
#[requires(x > 0)]
#[ensures(result > x)]
fn simple_negative(x: i32) -> i32 {
    x
}

// =============================================================================
// Phase 2: FnMut closures with postcondition_mut (mutable captures)
// =============================================================================

/// Call a FnMut closure once, with explicit postcondition_mut contract.
///
/// The `postcondition_mut` predicate takes four arguments:
///   postcondition_mut(pre_state, arg, post_state, result)
/// where `^f` is the prophecy/final value of the mutable borrow.
///
/// This is the simplest FnMut case: a single call with state change tracked
/// through the prophecy variable. Marked #[trusted] for Phase 2 baseline.
#[trusted]
#[requires((*f).precondition(x))]
#[ensures((*f).postcondition_mut(x, ^f, result))]
fn call_fn_mut_trusted<F: FnMut(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    f(x)
}

/// Call a FnMut closure once - NOT trusted.
///
/// The body `f(x)` compiles to `FnMut::call_mut(&mut f, (x,))`. The driver
/// looks up FnMut::call_mut's spec:
///   requires: (*self).precondition(arg)
///   ensures: (*self).postcondition_mut(arg, ^self, result)
///
/// After substitution at the call site:
///   requires: (*f).precondition(x)
///   ensures: (*f).postcondition_mut(x, ^f, call_result)
///
/// The substituted postcondition_mut becomes a call-site assumption, which
/// matches the function's ensures clause.
#[requires((*f).precondition(x))]
#[ensures((*f).postcondition_mut(x, ^f, result))]
fn call_fn_mut_verified<F: FnMut(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    f(x)
}

/// Negative test: wrong FnMut postcondition.
///
/// Claims `result > x` but FnMut::call_mut only provides
/// `postcondition_mut(x, ^f, result)` — there's no constraint
/// connecting result to x unless the caller's spec says so.
#[requires((*f).precondition(x))]
#[ensures(result > x)]
fn call_fn_mut_negative<F: FnMut(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    f(x)
}

/// Call a FnMut closure twice with explicit contracts (Phase 2 AC#1 & AC#3).
///
/// The body calls `f(x)` twice. In MIR, each call reborrows `f`:
///   call_1: FnMut::call_mut(&mut *f, (x,)) — reborrow r1, prophecy chain f_0 -> f_1
///   call_2: FnMut::call_mut(&mut *f, (x,)) — reborrow r2, prophecy chain f_1 -> f_2
///
/// Marked #[trusted] because verifying the prophecy chain for two successive
/// calls requires intermediate state reasoning that the non-trusted path
/// does not yet support (the solver must connect f_0 -> f_1 -> f_2 = ^f).
#[trusted]
#[requires((*f).precondition(x))]
#[ensures((*f).postcondition_mut(x, ^f, result))]
fn call_fn_mut_twice_trusted<F: FnMut(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    let _ = f(x);
    f(x)
}

// =============================================================================
// Phase 3: Annotated closure body verification
// =============================================================================

/// Positive Phase 3 case: inline closure contract matches closure body.
fn phase3_annotated_closure_positive() {
    let _closure = {
        #[requires(x > 0)]
        #[ensures(result == x + 1)]
        |x: i32| -> i32 { x + 1 }
    };
}

/// Negative Phase 3 case: inline closure contract is too strong.
fn phase3_annotated_closure_negative() {
    let _closure = {
        #[requires(x > 0)]
        #[ensures(result == x + 2)]
        |x: i32| -> i32 { x + 1 }
    };
}

/// Positive capture substitution case: contract references captured `y`.
fn phase3_capture_substitution_positive(y: i32) {
    let _closure = {
        #[requires(x > 0)]
        #[ensures(result == x + y)]
        |x: i32| -> i32 { x + y }
    };
}

/// Negative capture substitution case: captured-variable contract is too strong.
fn phase3_capture_substitution_negative(y: i32) {
    let _closure = {
        #[requires(x > 0)]
        #[ensures(result == x + y + 1)]
        |x: i32| -> i32 { x + y }
    };
}

// =============================================================================
// Phase 3 AC#4: Creusot 01_basic.rs-inspired patterns
// =============================================================================

/// Closure returning a captured variable (adapted from Creusot 01_basic.rs `uses_closure`).
///
/// Tests that a closure body consisting solely of a captured variable verifies
/// when the postcondition constrains result to equal the capture.
fn phase3_basic_capture_return(y: i32) {
    let _closure = {
        #[ensures(result == y)]
        || -> i32 { y }
    };
}

/// Multi-argument closure (adapted from Creusot 01_basic.rs `multi_arg`).
///
/// Tests closure body extraction with two parameters: `|a, b| a + b`.
fn phase3_basic_multi_arg_positive() {
    let _closure = {
        #[ensures(result == a + b)]
        |a: i32, b: i32| -> i32 { a + b }
    };
}

/// Multi-argument closure with incorrect postcondition (negative case).
/// Claims `result > a + b` but body computes exactly `a + b`.
fn phase3_basic_multi_arg_fails() {
    let _closure = {
        #[ensures(result > a + b)]
        |a: i32, b: i32| -> i32 { a + b }
    };
}

// =============================================================================
// Phase 3 AC#2 & AC#5: FnMut closure body with mutable capture
// Inspired by Creusot closures/07_mutable_capture.rs
// =============================================================================

/// FnMut closure that increments a captured variable.
///
/// The closure body mutates `x` (captured by &mut) and returns a value.
/// Postcondition expresses the final state of the capture: `x == old(x) + 1`.
fn phase3_fnmut_capture_increment_positive(mut x: i32) {
    let mut _closure = {
        #[requires(x < 1000)]
        #[ensures(x == old(x) + 1)]
        #[ensures(result == 5)]
        || -> i32 {
            x += 1;
            5
        }
    };
}

/// Negative FnMut case: claims wrong final capture value.
fn phase3_fnmut_capture_increment_negative(mut x: i32) {
    let mut _closure = {
        #[requires(x < 1000)]
        #[ensures(x == old(x) + 2)]
        #[ensures(result == 5)]
        || -> i32 {
            x += 1;
            5
        }
    };
}

// =============================================================================
// Phase 4: Resolve predicate for borrow termination
// =============================================================================

/// Positive resolve test: after incrementing a mutable reference,
/// the final value equals the initial value plus one. resolve(v) holds
/// when *v == ^v (current equals final), which is asserted implicitly
/// when the borrow ends.
///
/// This tests that `resolve(v)` in a postcondition correctly encodes as
/// `v_current == v_final` in SMT.
#[requires(*v > 0)]
#[ensures(^v == *v + 1)]
fn phase4_resolve_simple_positive(v: &mut i32) {
    *v += 1;
}

/// Positive test: call an FnOnce closure with resolve semantics.
///
/// The postcondition uses `postcondition_once`, which in the FnOnce
/// encoding means the closure is consumed and its captures resolve.
/// This is the simplest FnOnce pattern — trusted wrapper establishing
/// the `postcondition_once` result.
#[trusted]
#[requires(f.precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn call_fn_once_trusted<F: FnOnce(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Positive test: call an FnOnce closure via non-trusted path.
///
/// The body `f(x)` compiles to `FnOnce::call_once(f, (x,))`. The driver
/// looks up FnOnce::call_once's spec and injects postcondition_once
/// as a call-site assumption.
#[requires(f.precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn call_fn_once_verified<F: FnOnce(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Negative test: wrong FnOnce postcondition.
///
/// Claims `result > x` but FnOnce::call_once only provides
/// `postcondition_once(x, result)` — there's no constraint
/// connecting result to x unless the caller's spec says so.
#[requires(f.precondition(x))]
#[ensures(result > x)]
fn call_fn_once_negative<F: FnOnce(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

// =============================================================================
// Phase 4: fn_mut_once law — FnMut -> FnOnce weakening
// =============================================================================

/// Positive test: call an FnMut closure through FnOnce interface.
///
/// This is the key fn_mut_once weakening test. The function takes an FnMut
/// closure but the ensures clause uses `postcondition_once`. The fn_mut_once
/// law axiom connects them:
///   postcondition_once(self, args, result) <==>
///     exists res_state. postcondition_mut(self, args, res_state, result)
///                       && resolve(res_state)
///
/// Marked #[trusted] because the body uses FnMut::call_mut internally
/// but the contract speaks in FnOnce terms.
#[trusted]
#[requires((*f).precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn call_fn_mut_as_fn_once_trusted<F: FnMut(i32) -> i32>(mut f: F, x: i32) -> i32 {
    f(x)
}

/// Positive test: call an FnMut closure through FnOnce interface (non-trusted).
///
/// Same as `call_fn_mut_as_fn_once_trusted` but NOT marked `#[trusted]`.
/// The body `f(x)` compiles to `FnMut::call_mut(&mut f, (x,))`, which
/// gives us `postcondition_mut(f, x, ^f, call_0)` as a call-site assumption.
/// The fn_mut_once law axiom then bridges to the user-facing ensures clause:
///   postcondition_mut(self, args, res_state, result)
///     ==> postcondition_once(self, args, result)
///
/// This exercises the full FnMut->FnOnce weakening through the verification pipeline.
#[requires((*f).precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn call_fn_mut_as_fn_once_verified<F: FnMut(i32) -> i32>(mut f: F, x: i32) -> i32 {
    f(x)
}

/// Negative test: FnMut -> FnOnce with wrong postcondition.
///
/// Claims `result > x` but postcondition_once only provides the abstract
/// closure contract — no concrete bound on result relative to x.
#[requires((*f).precondition(x))]
#[ensures(result > x)]
fn call_fn_mut_as_fn_once_negative<F: FnMut(i32) -> i32>(mut f: F, x: i32) -> i32 {
    f(x)
}

// =============================================================================
// Phase 4: Fn closure laws — Fn -> FnMut -> FnOnce weakening chain
// =============================================================================

/// Positive test: Fn -> FnMut weakening via fn_mut law.
///
/// The fn_mut law says:
///   postcondition_mut(self, args, res_state, result) =
///     (postcondition(self, args, result) && self == res_state)
///
/// For an Fn closure, calling it doesn't change the closure state (self == res_state),
/// so postcondition_mut is equivalent to postcondition.
#[trusted]
#[requires(f.precondition(x))]
#[ensures(f.postcondition(x, result))]
fn call_fn_trusted<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Positive test: Fn -> FnOnce weakening via fn_once law.
///
/// The fn_once law says:
///   postcondition_once(self, args, result) =
///     (postcondition(self, args, result) && resolve(self))
///
/// This models the `weaken_std` -> `weaken_3_std` chain from Creusot's
/// `closures/06_fn_specs.rs`.
#[trusted]
#[requires(f.precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn call_fn_as_fn_once_trusted<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Positive test: Full Fn -> FnMut -> FnOnce weakening chain.
///
/// This tests the complete weakening chain from Creusot's 06_fn_specs.rs:
///   weaken_std (Fn, postcondition) -> weaken_2_std (FnMut, postcondition_mut)
///     -> weaken_3_std (FnOnce, postcondition_once)
///
/// Given postcondition(f, x, result) from an Fn closure, prove that
/// postcondition_once(f, x, result) holds. This exercises:
///   1. fn_once law: postcondition_once = postcondition && resolve(self)
///   OR the full chain:
///   1. fn_mut law: postcondition_mut = postcondition && (self == res_state)
///   2. fn_mut_once law: postcondition_once = exists res_state. postcondition_mut && resolve
///
/// Both paths should reach the same conclusion.
#[requires(f.precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn weaken_fn_to_fn_once<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Negative test: Fn postcondition does not constrain the result value.
///
/// Claims `result > x` but postcondition(f, x, result) only asserts the
/// abstract closure contract holds — it gives no concrete bound on result.
#[requires(f.precondition(x))]
#[ensures(result > x)]
fn call_fn_negative<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

// =============================================================================
// Phase 4c: Creusot 06_fn_specs.rs patterns — weakening at each trait level
// =============================================================================

/// FnMut -> FnOnce weakening with explicit FnMut call (by-value).
///
/// Adapted from Creusot's `weaken_2_std` -> `weaken_3_std` pattern.
/// Given an FnMut closure (which satisfies postcondition_mut via
/// FnMut::call_mut), prove that postcondition_once holds.
/// The fn_mut_once law connects them:
///   postcondition_once(self, args, result) <==>
///     exists res_state. postcondition_mut(self, args, res_state, result)
///                       && resolve(res_state)
///
/// This variant uses `mut f: F` (by-value with mut binding) — the same
/// pattern as Creusot's `weaken_2_std`.
#[requires((*f).precondition(a))]
#[ensures(f.postcondition_once(a, result))]
fn weaken_fn_mut_to_fn_once<F: FnMut(i32) -> i32>(mut f: F, a: i32) -> i32 {
    f(a)
}

/// Full Fn -> FnOnce weakening with postcondition in ensures.
///
/// Adapted from the complete chain in Creusot's 06_fn_specs.rs.
/// Takes an Fn closure (by value), calls it via Fn::call, and proves
/// postcondition_once. Exercises the full axiom chain:
///   fn_once law: postcondition_once(self, args, result) =
///     (postcondition(self, args, result) && resolve(self))
///
/// Unlike `weaken_fn_to_fn_once` (which also tests this), this variant
/// explicitly also asserts postcondition(f, a, result) in the ensures
/// to exercise both predicates simultaneously in the same encoding context.
#[requires(f.precondition(a))]
#[ensures(f.postcondition(a, result))]
#[ensures(f.postcondition_once(a, result))]
fn weaken_fn_both_postconditions<F: Fn(i32) -> i32>(f: F, a: i32) -> i32 {
    f(a)
}

/// Concrete FnOnce caller: tests that resolve is correctly compiled
/// when calling a function that takes FnOnce with a concrete closure.
///
/// Adapted from Creusot's `fn_once_user` + `caller` pattern in 06_fn_specs.rs.
/// The function takes FnOnce(i32) (unit return) with precondition on the argument.
/// The body calls f(0) which compiles to FnOnce::call_once(f, (0,)).
#[requires(f.precondition(0))]
fn fn_once_user<F: FnOnce(i32)>(f: F) {
    f(0)
}

// =============================================================================
// Phase 4c: Simplified 09_fnonce_resolve.rs patterns — FnOnce with resolve
// =============================================================================

/// FnOnce resolve through a generic function: the caller passes a
/// value and an FnOnce closure that transforms it.
///
/// Simplified from Creusot's `09_fnonce_resolve.rs` (no Box wrapping).
/// This tests that when a closure is consumed via FnOnce, the
/// postcondition_once predicate correctly captures the result.
#[trusted]
#[requires(f.precondition(x))]
#[ensures(f.postcondition_once(x, result))]
fn apply_fn_once_to_val<F: FnOnce(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Negative test: FnOnce resolve with incorrect postcondition.
///
/// Claims the result is greater than the input, but FnOnce's abstract
/// postcondition_once gives no such concrete bound.
#[requires(f.precondition(x))]
#[ensures(result > x)]
fn fnonce_resolve_negative<F: FnOnce(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

// =============================================================================
// Phase 5: Fn→FnMut weakening and advanced patterns
// =============================================================================

/// Fn → FnMut weakening: given an Fn closure (as `&mut F`), prove postcondition_mut.
///
/// The fn_mut law says:
///   postcondition_mut(self, args, res_state, result) =
///     (postcondition(self, args, result) && self == res_state)
///
/// For an Fn closure passed as &mut F, the FnMut::call_mut call provides
/// postcondition_mut. But the user contract only mentions postcondition_mut,
/// so the fn_mut law must fire to connect Fn's postcondition to FnMut's
/// postcondition_mut.
///
/// This is the `weaken_std` → `weaken_2_std` step from Creusot 06_fn_specs.rs.
#[requires((*f).precondition(x))]
#[ensures((*f).postcondition_mut(x, ^f, result))]
fn weaken_fn_to_fn_mut<F: Fn(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    f(x)
}

/// Negative: Fn → FnMut weakening with wrong postcondition.
///
/// Claims `result > x` but postcondition_mut only asserts the abstract
/// closure contract — no concrete bound on result.
#[requires((*f).precondition(x))]
#[ensures(result > x)]
fn weaken_fn_to_fn_mut_negative<F: Fn(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    f(x)
}

/// Non-trusted double FnMut call with prophecy chain.
///
/// The body calls `f(x)` twice. In MIR, each call reborrows `f`:
///   call_1: FnMut::call_mut(&mut *f, (x,)) — prophecy chain f_0 -> f_1
///   call_2: FnMut::call_mut(&mut *f, (x,)) — prophecy chain f_1 -> f_2
///
/// The ensures clause uses postcondition_mut with `^f` which should equal
/// the final state f_2 after both calls complete. This exercises prophecy
/// chaining through multiple reborrows.
///
/// NOT marked #[trusted] — this must verify through the call-site
/// assumption injection for both calls.
#[requires((*f).precondition(x))]
#[ensures((*f).postcondition_mut(x, ^f, result))]
fn call_fn_mut_twice_verified<F: FnMut(i32) -> i32>(f: &mut F, x: i32) -> i32 {
    let _ = f(x);
    f(x)
}

// =============================================================================
// Phase 6: Structural closure patterns — nested, move, multiple Fn calls
// Adapted from Creusot closures/ 01_basic, 02_nested, 03_generic_bound,
// 04_generic_closure, 08_multiple_calls
// =============================================================================

/// Move closure returning a captured variable (Creusot 01_basic.rs `move_closure` pattern).
///
/// The `move` keyword forces capture by value. For `i32` (Copy), the MIR is
/// identical to capture-by-ref, but verifying `move` closures ensures the
/// driver's closure-capture substitution works for both capture modes.
fn phase6_move_closure_positive(y: i32) {
    let _closure = {
        #[ensures(result == y)]
        move || -> i32 { y }
    };
}

/// Negative move closure: claims `result > y` but body returns `y`.
fn phase6_move_closure_negative(y: i32) {
    let _closure = {
        #[ensures(result > y)]
        move || -> i32 { y }
    };
}

/// Move closure capturing two variables and using both in computation.
fn phase6_move_closure_two_captures(a: i32, b: i32) {
    let _closure = {
        #[ensures(result == a + b)]
        move || -> i32 { a + b }
    };
}

/// Nested closure definition: outer function defines two closures at different
/// nesting levels. Both closures capture `y` from the enclosing function scope.
///
/// Adapted from Creusot 02_nested.rs: tests that the verifier handles closure
/// definitions within closure bodies without crashing. The inner closure is
/// only defined (not called) within the outer closure body — calling it would
/// require the inner closure to have a spec, which is a separate feature.
///
/// This tests that:
/// 1. The outer closure's contract correctly references the capture `y`
/// 2. The presence of an inner closure definition in the outer closure body
///    does not confuse the MIR extractor
fn phase6_nested_closure_define(y: i32) {
    let _outer = {
        #[ensures(result == y)]
        || -> i32 {
            let _inner = || -> i32 { y };
            y
        }
    };
}

/// Negative nested closure: claims result > y but body returns y.
fn phase6_nested_closure_define_negative(y: i32) {
    let _outer = {
        #[ensures(result > y)]
        || -> i32 {
            let _inner = || -> i32 { y };
            y
        }
    };
}

/// Multiple Fn calls: calling a pure Fn closure twice should be sound because
/// Fn closures don't mutate state (Creusot 08_multiple_calls.rs pattern).
///
/// Unlike FnMut (which requires prophecy chaining), Fn closures can be called
/// any number of times with the same postcondition. The `postcondition` for
/// the second call is the same uninterpreted predicate as the first.
#[trusted]
#[requires(f.precondition(x))]
#[ensures(f.postcondition(x, result))]
fn call_fn_twice_trusted<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    let _ = f(x);
    f(x)
}

/// Multiple Fn calls (non-trusted): the body calls `f(x)` twice via Fn::call.
///
/// Both calls produce the same postcondition(f, x, result) assumption because
/// Fn::call's spec is pure (no state change). The second call's result is the
/// function return value, and postcondition(f, x, result) should hold.
#[requires(f.precondition(x))]
#[ensures(f.postcondition(x, result))]
fn call_fn_twice_verified<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    let _ = f(x);
    f(x)
}

/// Negative: multiple Fn calls with wrong postcondition.
///
/// Claims `result > x` but Fn postcondition gives no concrete bound.
#[requires(f.precondition(x))]
#[ensures(result > x)]
fn call_fn_twice_negative<F: Fn(i32) -> i32>(f: &F, x: i32) -> i32 {
    let _ = f(x);
    f(x)
}

/// Generic Fn bound with unit return (Creusot 03_generic_bound.rs pattern).
///
/// Tests closure dispatch with a `Fn(i32)` bound (unit return type).
/// The ensures clause is trivially true — this exercises the encoder's
/// handling of unit-return closures without tripping on sort mismatches.
#[trusted]
#[requires(f.precondition(x))]
fn apply_fn_unit_trusted<F: Fn(i32)>(f: &F, x: i32) {
    f(x)
}

/// Non-trusted unit-return Fn call.
///
/// The body `f(x)` compiles to `Fn::call(f, (x,))` with unit return.
/// The call-site assumption injection must handle the unit return type
/// correctly (no postcondition value constraint, only precondition check).
#[requires(f.precondition(x))]
fn apply_fn_unit_verified<F: Fn(i32)>(f: &F, x: i32) {
    f(x)
}

