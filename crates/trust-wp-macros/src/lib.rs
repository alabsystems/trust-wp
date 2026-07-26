// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]

//! trust-wp Macros - Contract attribute macros
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This crate provides proc macros for specifying contracts:
//! - `#[requires(...)]` - Preconditions
//! - `#[ensures(...)]` - Postconditions
//! - `#[invariant(...)]` - Loop/type invariants
//! - `#[variant(...)]` - Termination variants (decreasing expressions)
//! - `#[logic]` / `#[predicate]` - Specification-only pure functions
//! - `#[law]` - Type-level axioms (Creusot compatibility alias)
//! - `#[opaque]` - Hide logic function body from callers
//! - `#[erasure]` - Relate spec-enriched function to runtime counterpart
//! - `#[trusted]` - Trust function implementation without verification
//! - `#[check]` - Runtime assertion checking
//! - `#[bitwise_proof]` - Bitvector-mode verification marker (Creusot compat)
//! - `#[builtin("name")]` - Built-in primitive marker (Creusot compat)
//! - `#[maintains(...)]` - Maintains clause marker (Creusot compat)
//! - `#[open_inv_result]` - Suppress result-type invariant injection
//! - `DeepModel` (derive) - Generate companion deep model type
//! - `Default` (derive) - Generate a Creusot-compatible default impl
//! - `ghost!(...)` - Ghost code blocks (erased at compile time)
//! - `snapshot!(...)` - Capture values at specific program points
//! - `ghost_let!(...)` - Declare ghost variables (erased at compile time)
//! - `proof_assert!(...)` - Assertions checked by the prover
//! - `__trust_wp_trusted_proof_assert!(...)` - Internal: trusted proof assertions
//! - `pearlite!(...)` - Specification-language expressions
//! - `extern_spec!(...)` - Specifications for external functions
//!
//! # Contract Extraction
//!
//! The trust-wp driver extracts contracts directly from the source AST.
//! On success, these proc macros validate contract syntax at compile time and
//! pass through the item unchanged. Invalid contracts emit compile errors.
//!
//! # Example
//!
//! Examples import `trust_wp_macros` directly so doctests can compile in this crate.
//!
//! ```rust,no_run
//! use trust_wp_macros::{ensures, requires};
//!
//! #[requires(x > 0)]
//! #[ensures(result == old(x) + 1)]
//! fn increment(x: i32) -> i32 {
//!     x + 1
//! }
//! ```

use proc_macro::TokenStream;

mod attrs;
mod contract;
mod deep_model;
mod default;
mod expr_walk;
mod extern_spec;
mod extern_spec_helpers;
mod ghost;
mod ghost_macros;
mod logic;
mod logic_emit;
mod marker_attrs;
mod pearlite;
mod snapshot_rewrite;
mod transform;
mod view_syntax;

#[cfg(test)]
mod expr_walk_tests;
#[cfg(test)]
mod snapshot_rewrite_tests;

// ── Contract attributes ──────────────────────────────────────────────

/// Specifies a precondition that must hold when a function is called.
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    attrs::requires(&attr, item)
}

/// Specifies a postcondition that must hold when a function returns.
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    attrs::ensures(&attr, item)
}

/// Specifies a loop invariant that must hold at each iteration.
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    attrs::invariant(&attr, item)
}

/// Specifies a termination variant for loops or recursive functions.
#[proc_macro_attribute]
pub fn variant(attr: TokenStream, item: TokenStream) -> TokenStream {
    attrs::variant(&attr, item)
}

// ── Logic function attributes ────────────────────────────────────────

/// Marks a function as a pure specification-only logic function.
///
/// Logic functions exist only for verification and are erased at compile time.
/// They can be called from contracts (`#[requires]`, `#[ensures]`) and ghost blocks.
///
/// # Properties
///
/// - **Pure**: No side effects, no mutable parameters
/// - **Unbounded arithmetic**: Can use `Int` for specification precision
/// - **Ghost-only**: Cannot be called from runtime code
/// - **Erased**: Not present in compiled binary (body replaced with `unreachable!()`)
///
/// # Example
///
/// ```rust,no_run
/// use trust_wp_macros::logic;
///
/// #[logic]
/// fn max(a: i32, b: i32) -> i32 {
///     if a >= b {
///         a
///     } else {
///         b
///     }
/// }
/// ```
///
/// See `designs/2026-02-01-logic-functions.md` and Issue #153.
#[proc_macro_attribute]
pub fn logic(attr: TokenStream, item: TokenStream) -> TokenStream {
    logic_emit::process_logic(&attr, item)
}

/// Marks a logic function as a predicate (must return `bool`).
///
/// Equivalent to `#[logic]` plus a return-type check.
#[proc_macro_attribute]
pub fn predicate(attr: TokenStream, item: TokenStream) -> TokenStream {
    logic_emit::process_predicate(&attr, item)
}

/// Declares a law (axiom) function.
///
/// Creusot compatibility attribute: equivalent to `#[logic(open)]`.
/// The function body is treated as an axiom source and remains visible to SMT
/// encoding so its defining axiom is emitted.
#[proc_macro_attribute]
pub fn law(attr: TokenStream, item: TokenStream) -> TokenStream {
    logic_emit::process_law(&attr, item)
}

// ── Marker attributes ────────────────────────────────────────────────

/// Marks a logic function or type as opaque to callers.
///
/// Opaque functions are declared in SMT but their defining axioms are not emitted.
/// For types, this hides the type's structure from verification.
#[proc_macro_attribute]
pub fn opaque(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_opaque(&attr, item)
}

/// Marks a type or function as erased during compilation.
///
/// `#[erasure(target)]` relates a spec-enriched function to its runtime counterpart.
/// Compatibility stub: preserved as a doc marker for driver detection.
#[proc_macro_attribute]
pub fn erasure(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_erasure(&attr, item)
}

/// Marks a function as trusted (axiomatically correct without verification).
///
/// When a function is marked `#[trusted]`:
/// - Preconditions are checked at call sites (not trusted)
/// - Postconditions are **assumed** correct (not verified)
/// - The function body is NOT analyzed by the verifier
///
/// See Issue #230 for the design discussion.
#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_trusted(&attr, item)
}

/// Marks a function as checked in a specific mode (e.g., ghost).
///
/// Compatibility stub: preserved as a doc marker for driver detection.
#[proc_macro_attribute]
pub fn check(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_check(&attr, item)
}

/// Marks a function for bitvector-mode verification.
///
/// Creusot compatibility: pass-through marker preserving the item unchanged.
/// Real bitvector solver routing is tracked separately.
#[proc_macro_attribute]
pub fn bitwise_proof(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_bitwise_proof(&attr, item)
}

/// Marks an item as a built-in primitive (Creusot compat).
///
/// `#[builtin("name")]` tells the verifier that the function or type
/// corresponds to a primitive in the target prover (a Why3 theory operator
/// or an SMT theory function). trust-wp accepts the attribute and records it
/// as a `trust-wp:builtin:<name>:` doc marker; the item itself is passed
/// through unchanged. Real intrinsic dispatch is handled separately.
#[proc_macro_attribute]
pub fn builtin(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_builtin(&attr, item)
}

/// Desugars a `#[maintains(P)]` clause into `#[requires(P)] #[ensures(P)]`.
///
/// Creusot compatibility: `mut` in the maintains clause becomes `*` (deref)
/// in the precondition and `^` (final value) in the postcondition.
#[proc_macro_attribute]
pub fn maintains(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_maintains(&attr, item)
}

/// Suppresses result-type invariant injection for a function.
///
/// When a function returns a type with an invariant (e.g., NonZeroU64),
/// the verifier normally adds the type invariant as a postcondition.
/// `#[open_inv_result]` suppresses this injection.
#[proc_macro_attribute]
pub fn open_inv_result(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_open_inv_result(&attr, item)
}

/// Marks a function as requiring termination proof.
///
/// Standalone alias for `#[check(terminates)]`. Functions marked
/// `#[terminates]` must not call non-terminating functions, and any
/// loops or recursive calls must have `#[variant]` clauses that
/// strictly decrease.
#[proc_macro_attribute]
pub fn terminates(attr: TokenStream, item: TokenStream) -> TokenStream {
    marker_attrs::process_terminates(&attr, item)
}

// ── Derive macros ────────────────────────────────────────────────────

/// Derives the `DeepModel` trait, generating a companion "deep model" type.
#[proc_macro_derive(DeepModel, attributes(DeepModelTy))]
pub fn derive_deep_model(input: TokenStream) -> TokenStream {
    deep_model::derive_deep_model(input)
}

/// Derives `Default` using the Creusot-compatible derive semantics.
#[proc_macro_derive(Default, attributes(default))]
pub fn derive_default(input: TokenStream) -> TokenStream {
    default::derive_default(input)
}

// ── Function-like macros ─────────────────────────────────────────────

/// Marks a block as ghost code (verification only, erased at compile time).
///
/// See `designs/2026-02-01-ghost-code.md` and `designs/2026-02-02-ghost-macro-stable-rust.md`.
#[proc_macro]
pub fn ghost(input: TokenStream) -> TokenStream {
    ghost_macros::expand_ghost(input)
}

/// Captures a snapshot of a value for proof purposes.
///
/// See `designs/2026-02-01-snapshot-type.md`.
#[proc_macro]
pub fn snapshot(input: TokenStream) -> TokenStream {
    ghost_macros::expand_snapshot(input)
}

/// Declares a ghost variable (verification only, erased at compile time).
///
/// Shorthand for `let var = ghost! { expr };` with special handling for
/// type invariant checking (`ghost_let` bypasses invariant checking on the result).
///
/// # Syntax
///
/// ```text
/// ghost_let!(var = expr);
/// ghost_let!(mut var = expr);
/// ```
///
/// Reference: Creusot `creusot-std-proc/src/common.rs:117-131`
#[proc_macro]
pub fn ghost_let(input: TokenStream) -> TokenStream {
    ghost_macros::expand_ghost_let(input)
}

/// Inserts a proof assertion checked by the SMT solver.
///
/// See `creusot-compatibility.md` at the repo root.
#[proc_macro]
pub fn proof_assert(input: TokenStream) -> TokenStream {
    ghost_macros::expand_proof_assert(input)
}

/// The in-source authored-proof surface (design §3 L1): `proof!(by <tactic>)` or
/// `proof!(assume [<axioms>], by <tactic>)`.
///
/// Desugars to a reserved `trust-wp:proof_by:` marker using the `proof_assert!`
/// mechanism. The production driver does not currently consume this marker, so
/// this macro is an inert proof hint and cannot discharge an obligation.
#[proc_macro]
pub fn proof(input: TokenStream) -> TokenStream {
    ghost_macros::expand_proof(input)
}

/// Assumes a proposition without proof — the incremental-development escape hatch.
///
/// `assume!(expr)` lowers to the trusted-proof-assertion path: the driver treats it as
/// an assumption, and the honesty meter HARD-CAPS every downstream grade at `Trusted`
/// (the assumption is named in the axiom closure — visible, never silent). This is the
/// Verus `assume()` shape made honest: you can scaffold a proof incrementally, but the
/// meter never forgets what you owe.
#[proc_macro]
pub fn assume(input: TokenStream) -> TokenStream {
    ghost_macros::expand_trusted_proof_assert(input)
}

/// Internal helper emitted by `#[trusted]` for trusted proof assertions.
#[proc_macro]
#[doc(hidden)]
pub fn __trust_wp_trusted_proof_assert(input: TokenStream) -> TokenStream {
    ghost_macros::expand_trusted_proof_assert(input)
}

/// Embeds a specification-only expression using pearlite DSL syntax.
///
/// See `designs/2026-02-02-pearlite-dsl.md` and Issue #245.
#[proc_macro]
pub fn pearlite(input: TokenStream) -> TokenStream {
    let expr = match pearlite::validate_pearlite_expr(&input) {
        Ok(e) => e,
        Err(e) => {
            return syn::Error::new(e.span, format!("pearlite!: {}", e.message()))
                .to_compile_error()
                .into();
        }
    };
    pearlite::expand_pearlite(&expr).into()
}

// R1 (two-language spec surface): the `verus!{}` block front-end is
// deleted — zero consumers; the Verus surface is retired per the ratified
// two-language spec-surface design (§3.2/R1). The native surface is
// first-class trustc clauses (R3); the Verus corpus survives as engine
// test material.

/// Specifies contracts for external (unowned) functions.
///
/// See `designs/2026-02-01-extern-spec.md` and Issue #160.
#[proc_macro]
pub fn extern_spec(input: TokenStream) -> TokenStream {
    let parsed = match syn::parse(input) {
        Ok(p) => p,
        Err(e) => return e.to_compile_error().into(),
    };
    match extern_spec::expand_extern_spec(parsed) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}
