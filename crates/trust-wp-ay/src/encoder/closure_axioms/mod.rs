// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure trait axioms — the **UF fallback path** for the SMT encoder.
//!
//! # Dual-Path Architecture (#2151)
//!
//! Closure encoding uses two parallel paths, selected per-closure at call sites
//! in `method_call/mod.rs`:
//!
//! 1. **Body inlining** (`closure_inline.rs`): For closures with MIR bodies
//!    extracted by the driver, the postcondition is encoded as a ground term
//!    `result == body_expr`. This eliminates all quantifiers and is the primary
//!    path for same-crate closures. Handles `postcondition`, `postcondition_once`,
//!    and `postcondition_mut`.
//!
//! 2. **UF axiom fallback** (this module): For closures without extractable
//!    bodies (cross-crate, opaque, or Box-wrapped), postconditions are encoded as
//!    uninterpreted Bool-returning functions with quantified hierarchy axioms.
//!    This path declares UF symbols which trigger demand-driven axiom emission
//!    in `assert_standard_axioms`.
//!
//! When body inlining handles all closures in a VC, **no UF symbols are
//! declared** and the entire axiom machinery is skipped — the demand guards
//! (`has_closure_postcondition_*_symbols`) return false.
//!
//! # Contents
//!
//! - Sort tag encoding/decoding for closure-spec UF symbol names
//! - Closure specification method encoding (precondition, postcondition, etc.)
//! - Fn/FnMut/FnOnce hierarchy laws (weakening chain) — `fn_laws.rs`
//! - Eager instantiation of fn_mut_once reverse axiom — `fn_mut_once.rs`
//! - Existential Skolemization for postcondition_mut assumptions — `fn_mut_once.rs`
//! - Closure resolve axioms (structural decomposition) — `resolve.rs`
//! - hist_inv axioms (per-capture identity constraints)
//! - PureExpr tree walkers for postcondition_mut detection — `expr_walkers.rs`
//!
//! Extracted from `axioms.rs` as part of #1528 decomposition (Phase 1).
//! Further decomposed into submodules as part of #1988.

mod expr_walkers;
mod fn_laws;
mod fn_mut_once;
mod fn_mut_once_eager;
mod fn_mut_once_skolem;
mod resolve;

use std::fmt::Write as _;

use ay_dpll::api::{FuncDecl, Sort, Term};
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::{closure_sorts::closure_env_sort_name, unsoundness, AYEncoder};
use crate::error::EncodingError;

const DEFAULT_POSTCONDITION_RECEIVER: &str = "core::default::Default::default";

/// Recursively peel all `Deref` layers from a closure receiver expression.
///
/// Box-wrapped closures (e.g., `Box::new(f)`) introduce extra `Deref` layers
/// in MIR because `Box<F>` implements `Deref<Target = F>`. The Fn::call spec
/// adds another `(*self)` deref on top. This produces chains like
/// `Deref(Deref(Var("f")))` where only one layer was previously peeled,
/// causing the closure UF symbol to reference `f_current` instead of `f`.
/// The resulting symbol mismatch disconnects the callee's postcondition
/// assumption from the caller's postcondition goal. (#1373)
///
/// This function normalizes all deref layers so that `f.postcondition(...)`,
/// `(*f).postcondition(...)`, and `(**f).postcondition(...)` all encode to
/// the same UF symbol with receiver `f`.
pub(crate) fn normalize_closure_receiver(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Deref(inner) => normalize_closure_receiver(inner),
        _ => expr,
    }
}

fn is_default_postcondition_receiver_alias(expr: &PureExpr) -> bool {
    let PureExpr::Var(name, _) = expr else {
        return false;
    };

    // Creusot-compatible specs can spell the same Default trait receiver as
    // `core::default::Default::default` in call assumptions and `T::default`
    // in the callee postcondition. Keep their closure-spec UF receiver shared.
    matches!(
        name.as_str(),
        DEFAULT_POSTCONDITION_RECEIVER | "std::default::Default::default" | "Default::default"
    ) || name
        .strip_suffix("::default")
        .is_some_and(|ty| ty.len() == 1 && ty.chars().all(|c| c.is_ascii_uppercase()))
}

/// Result of single-pass `closure_postcondition_*` demand guard scan (#2278 F5).
#[derive(Debug, Default)]
pub(crate) struct ClosurePostconditionFlags {
    pub(crate) has_once: bool,
    pub(crate) has_fn: bool,
    pub(crate) has_mut: bool,
}

/// Pre-parsed `closure_postcondition_mut_*` declaration from `logic_funcs` (#2278 F3).
///
/// Collected once per axiom-emission pass so that `matching_postcondition_mut_symbols`
/// filters a small vec instead of scanning all `logic_funcs` per `postcondition_once`.
struct ParsedMutDecl {
    name: String,
    decl: FuncDecl,
    arity: usize,
    tags: Vec<String>,
    sorts: Vec<Sort>,
}

fn normalize_logic_name(name: &str) -> String {
    name.strip_prefix("logic_")
        .unwrap_or(name)
        .replace("__", "_")
}

impl AYEncoder {
    #[track_caller]
    fn note_closure_axiom_skipped(context: &str) {
        unsoundness::increment(unsoundness::UnsoundnessCategory::ClosureAxiomSkipped);

        let loc = std::panic::Location::caller();
        debug!(
            "[TRUST_WP_DEBUG] ClosureAxiomSkipped at {}:{}:{} ({context})",
            loc.file(),
            loc.line(),
            loc.column()
        );
    }

    pub(crate) fn axiom_apply_tracked(
        &mut self,
        context: &str,
        func: &FuncDecl,
        args: &[Term],
    ) -> Option<Term> {
        let term = self.axiom_apply(context, func, args);
        if term.is_none() {
            Self::note_closure_axiom_skipped(context);
        }
        term
    }

    /// Compatibility entry point for closure-law applications whose producers
    /// can disagree about domain sorts.
    ///
    /// Closure-spec UF declarations (`postcondition`, `postcondition_mut`,
    /// `postcondition_once`) can have divergent domain sorts for the same
    /// logical parameter because `encode_closure_spec_method` uses a hybrid
    /// inferred/actual sort scheme that depends on the call-site context.
    /// The fn_law axiom builders create quantifier variables from one
    /// declaration's domain and apply them to another — which can fail the
    /// strict sort check in `try_apply`. An older implementation constructed a
    /// second `FuncDecl` with the same symbol name and argument-derived sorts.
    /// That handle was never declared in the solver and therefore had no typed
    /// identity linking it to `func`; accepting it could attach an axiom to the
    /// wrong function signature. AY 0.2 rejects such unauthenticated handles.
    /// Keep the fast path, but fail closed on every mismatch by omitting the
    /// optional premise axiom and recording the conservative skip. (#2556)
    pub(crate) fn axiom_apply_sort_adapted(
        &mut self,
        context: &str,
        func: &FuncDecl,
        args: &[Term],
    ) -> Option<Term> {
        // Fast path: the authenticated declaration and argument sorts match.
        if let term @ Some(_) = self.axiom_apply(context, func, args) {
            return term;
        }

        Self::note_closure_axiom_skipped(context);
        None
    }

    /// Predeclare the `postcondition_mut` companion for any selected closure
    /// postcondition when mut-borrow current/final vars are already present.
    ///
    /// This keeps the matching `closure_postcondition_mut_*` symbol alive
    /// before goal encoding, so the mut-borrow compat path does not encode the
    /// postcondition through an unconstrained placeholder UF and then try to
    /// repair it later with closure-law synthesis. (#6)
    pub(crate) fn predeclare_closure_postcondition_mut_companions(
        &mut self,
        needs_companion: bool,
    ) {
        if !needs_companion {
            return;
        }

        let closure_posts: Vec<_> = self
            .logic_funcs_iter()
            .filter(|(name, _)| {
                let logical_name = normalize_logic_name(name);
                logical_name.starts_with("closure_postcondition_")
                    && !logical_name.starts_with("closure_postcondition_once_")
                    && !logical_name.starts_with("closure_postcondition_mut_")
            })
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();

        if crate::trust_wp_debug_enabled() {
            eprintln!(
                "[TRUST_WP_DEBUG] predeclare_closure_postcondition_mut_companions: \
                 needs_companion={needs_companion}, closure_posts={}",
                closure_posts.len()
            );
        }

        for (post_name, post_decl) in closure_posts {
            let logical_name = normalize_logic_name(&post_name);
            let Some(suffix) = logical_name.strip_prefix("closure_postcondition_") else {
                continue;
            };
            let Some((arity_raw, sort_sig)) = suffix.split_once('_') else {
                continue;
            };
            let Ok(post_arity) = arity_raw.parse::<usize>() else {
                continue;
            };
            let sort_tags: Vec<&str> = sort_sig.split('_').collect();
            if sort_tags.len() != post_arity || sort_tags.is_empty() {
                continue;
            }

            let mut mut_tags = sort_tags
                .iter()
                .map(|tag| (*tag).to_string())
                .collect::<Vec<_>>();
            let insert_pos = mut_tags.len() - 1;
            mut_tags.insert(insert_pos, sort_tags[0].to_string());
            let mut_source_name = format!(
                "closure_postcondition_mut_{}_{}",
                post_arity + 1,
                mut_tags.join("_")
            );
            let mut_registry_name = if post_name.starts_with("logic_") {
                trust_wp_core::logic::logic_fn_smt_name(&mut_source_name)
            } else {
                mut_source_name.clone()
            };
            if self.logic_func_decl_cloned(&mut_registry_name).is_some()
                || self.logic_func_decl_cloned(&mut_source_name).is_some()
            {
                continue;
            }

            let mut_domain: Vec<Sort> = {
                let mut domain = post_decl.domain().to_vec();
                let res_state_idx = post_arity - 1;
                domain.insert(res_state_idx, post_decl.domain()[0].clone());
                domain
            };
            let _ = self.get_or_declare_logic_func(&mut_registry_name, &mut_domain, Sort::Bool);
        }
    }

    /// Closure-spec methods (`precondition`, `postcondition`, `postcondition_once`,
    /// `postcondition_mut`) are specification-only predicates from the `FnExt`/
    /// `FnOnceExt`/`FnMutExt` extension traits. They are encoded as uninterpreted
    /// SMT functions that return Bool.
    ///
    /// Example: `f.postcondition((x,), result)` becomes
    /// `(closure_postcondition f x result)` in SMT.
    pub(crate) fn closure_sort_tag(sort: &Sort) -> String {
        match sort {
            Sort::Bool => "b".to_string(),
            Sort::Int => "i".to_string(),
            _ => {
                // Closure env sorts (both Datatype and Uninterpreted representations)
                // need per-sort disambiguation in symbol names (#2151).
                if let Some(name) = closure_env_sort_name(sort) {
                    let mut tag = String::from("c");
                    for byte in name.as_bytes() {
                        let _ = write!(&mut tag, "{byte:02x}");
                    }
                    return tag;
                }
                // Backward-compatible fallback for non-closure sorts.
                "u".to_string()
            }
        }
    }

    /// Decode a sort tag back to a ay `Sort`.
    ///
    /// **Warning:** This round-trip is lossy. `"u"` decodes to `Sort::Int` (the
    /// universal default), and `"c..."` decodes to `Sort::Uninterpreted` even
    /// though registered closure sorts are `Sort::Datatype`. For actual UF domain
    /// sorts, prefer `FuncDecl::domain()` instead. (#2151 Phase 4)
    ///
    /// Retained for test coverage of sort-tag encoding and backward compatibility
    /// with symbol-name parsing. Not called from production encoder paths.
    #[cfg(test)]
    pub(crate) fn closure_sort_from_tag(tag: &str) -> Option<Sort> {
        match tag {
            "b" => Some(Sort::Bool),
            "i" => Some(Sort::Int),
            // "u" = uninterpreted (non-Bool/non-Int). The encoder uses Int as the
            // universal SMT sort for uninterpreted types (#599).
            "u" => Some(Sort::Int),
            _ if tag.starts_with('c') => {
                let encoded = tag.strip_prefix('c')?;
                if encoded.len() % 2 != 0 {
                    return None;
                }
                let mut bytes = Vec::with_capacity(encoded.len() / 2);
                for chunk in encoded.as_bytes().as_chunks::<2>().0 {
                    let hex = std::str::from_utf8(chunk).ok()?;
                    let byte = u8::from_str_radix(hex, 16).ok()?;
                    bytes.push(byte);
                }
                let sort_name = String::from_utf8(bytes).ok()?;
                Some(Sort::Uninterpreted(sort_name))
            }
            _ => None,
        }
    }

    fn parse_closure_signature(name: &str, prefix: &str) -> Option<(usize, Vec<String>)> {
        let suffix = name.strip_prefix(prefix)?;
        let (arity_raw, sort_sig) = suffix.split_once('_')?;
        let arity = arity_raw.parse::<usize>().ok()?;
        let sort_tags = sort_sig
            .split('_')
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        if sort_tags.len() != arity {
            return None;
        }
        Some((arity, sort_tags))
    }

    fn mut_signature_matches_once(once_tags: &[String], mut_tags: &[String]) -> bool {
        if once_tags.is_empty() || mut_tags.len() != once_tags.len() + 1 {
            return false;
        }
        let insert_pos = once_tags.len() - 1;
        // Strategy B (#1997): require identity-only matching for closure-env
        // res_state sorts. When res_state is a closure env type ("c..." tag),
        // it must equal the self sort (position 0) to prevent cross-type axiom
        // pairs where two closure types with compatible arg/return sorts but
        // different env sorts would incorrectly share fn_mut_once axioms.
        //
        // Primitive res_state sorts (Bool "b", Int "i", uninterpreted "u") are
        // exempt: these represent non-env intermediate state values and cannot
        // cause cross-type aliasing. (#1965, Category A Bool-sort fix)
        if let Some(res_tag) = mut_tags.get(insert_pos) {
            if res_tag.starts_with('c') && mut_tags.get(insert_pos) != mut_tags.first() {
                return false;
            }
        }
        once_tags.iter().enumerate().all(|(i, once_tag)| {
            let mut_idx = if i < insert_pos { i } else { i + 1 };
            mut_tags
                .get(mut_idx)
                .is_some_and(|mut_tag| mut_tag == once_tag)
        })
    }

    /// Collect all parsed `closure_postcondition_mut_*` entries from `logic_funcs`
    /// in a single O(N) pass (#2278 F3). Callers filter this pre-collected vec
    /// via `matching_postcondition_mut_symbols` instead of re-scanning all
    /// `logic_funcs` per `postcondition_once` symbol.
    fn collect_postcondition_mut_entries(&self) -> Vec<ParsedMutDecl> {
        self.logic_funcs_iter()
            .filter_map(|(name, decl)| {
                let logical_name = normalize_logic_name(name);
                let (arity, tags) =
                    Self::parse_closure_signature(&logical_name, "closure_postcondition_mut_")?;
                let sorts = decl.domain().to_vec();
                Some(ParsedMutDecl {
                    name: name.clone(),
                    decl: decl.clone(),
                    arity,
                    tags,
                    sorts,
                })
            })
            .collect()
    }

    fn matching_postcondition_mut_symbols(
        mut_entries: &[ParsedMutDecl],
        once_arity: usize,
        once_tags: &[String],
    ) -> Vec<(String, FuncDecl, Vec<String>, Vec<Sort>)> {
        let mut matches: Vec<_> = mut_entries
            .iter()
            .filter(|entry| {
                entry.arity == once_arity + 1
                    && Self::mut_signature_matches_once(once_tags, &entry.tags)
            })
            .map(|entry| {
                (
                    entry.name.clone(),
                    entry.decl.clone(),
                    entry.tags.clone(),
                    entry.sorts.clone(),
                )
            })
            .collect();
        matches.sort_by(|a, b| a.0.cmp(&b.0));
        matches
    }

    fn fn_mut_once_witness_name(
        once_arity: usize,
        once_sort_sig: &str,
        res_state_tag: &str,
    ) -> String {
        if res_state_tag == "i" {
            format!("fn_mut_once_witness_{once_arity}_{once_sort_sig}")
        } else {
            format!("fn_mut_once_witness_{once_arity}_{once_sort_sig}_{res_state_tag}")
        }
    }

    /// Check whether any `postcondition_once` closure symbols have been declared.
    /// Delegates to `closure_postcondition_flags()` for single-pass efficiency.
    #[cfg(test)]
    pub(crate) fn has_closure_postcondition_once_symbols(&self) -> bool {
        self.closure_postcondition_flags().has_once
    }

    /// Check whether any Fn-trait `postcondition` closure symbols have been declared
    /// (excluding `postcondition_once` and `postcondition_mut`).
    /// Delegates to `closure_postcondition_flags()` for single-pass efficiency.
    #[cfg(test)]
    pub(crate) fn has_closure_postcondition_fn_symbols(&self) -> bool {
        self.closure_postcondition_flags().has_fn
    }

    /// Check whether any `postcondition_mut` closure symbols have been declared.
    /// Delegates to `closure_postcondition_flags()` for single-pass efficiency.
    #[cfg(test)]
    pub(crate) fn has_closure_postcondition_mut_symbols(&self) -> bool {
        self.closure_postcondition_flags().has_mut
    }

    /// Single-pass demand guard scan: classifies all `closure_postcondition_*`
    /// symbols in `logic_funcs` in one O(N) traversal instead of 3× O(N). (#2278 F5)
    pub(crate) fn closure_postcondition_flags(&self) -> ClosurePostconditionFlags {
        let mut flags = ClosurePostconditionFlags::default();
        for name in self.logic_func_names_iter() {
            let logical_name = normalize_logic_name(name);
            if !logical_name.starts_with("closure_postcondition_") {
                continue;
            }
            if logical_name.starts_with("closure_postcondition_once_") {
                flags.has_once = true;
            } else if logical_name.starts_with("closure_postcondition_mut_") {
                flags.has_mut = true;
            } else {
                flags.has_fn = true;
            }
            if flags.has_once && flags.has_fn && flags.has_mut {
                break;
            }
        }
        flags
    }

    /// Build a unique SMT function symbol for a closure-spec method signature.
    ///
    /// Closure-spec methods are overloaded by trait context and argument tuple.
    /// SMT function symbols are not overloaded, so we include the arity and a
    /// coarse sort signature in the symbol to avoid collisions.
    fn closure_spec_symbol(method: &str, param_sorts: &[Sort]) -> String {
        let sort_signature = param_sorts
            .iter()
            .map(Self::closure_sort_tag)
            .collect::<Vec<String>>()
            .join("_");
        format!("closure_{method}_{}_{}", param_sorts.len(), sort_signature)
    }

    /// Encode a closure spec method as an uninterpreted Bool-returning function.
    ///
    /// This is the **UF fallback path** — used only when `try_inline_closure_postcondition`
    /// in `closure_inline.rs` returns `None` (no extractable MIR body). Declaring a UF
    /// symbol here triggers demand-driven axiom emission in `assert_standard_axioms`.
    pub(super) fn encode_closure_spec_method(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Normalize all deref layers so `f.postcondition(...)`,
        // `(*f).postcondition(...)`, and `(**f).postcondition(...)` (Box-wrapped)
        // all encode to the same predicate term. (#1373)
        let normalized_receiver = normalize_closure_receiver(receiver);
        let canonical_default_receiver = if method == "postcondition"
            && is_default_postcondition_receiver_alias(normalized_receiver)
        {
            Some(PureExpr::Var(
                DEFAULT_POSTCONDITION_RECEIVER.to_string(),
                None,
            ))
        } else {
            None
        };
        let spec_receiver = canonical_default_receiver
            .as_ref()
            .unwrap_or(normalized_receiver);
        let receiver_term = self.encode_pure_impl(spec_receiver, prefix)?;
        let arg_terms: Vec<Term> = args
            .iter()
            .map(|arg| self.encode_pure_impl(arg, prefix))
            .collect::<Result<Vec<_>, _>>()?;

        // Build all argument terms: receiver first, then method args
        let mut all_terms = vec![receiver_term];
        all_terms.extend(arg_terms);

        // Receiver/args can vary across closure traits (e.g., precondition() vs
        // precondition(arg)). Use signature-specific symbols to avoid arity/sort
        // collisions in debug assertions and the SMT context.
        //
        // Reconcile inferred sorts with actual term sorts. The UF domain must
        // match the actual argument term sorts in the solver, so prefer `actual`
        // whenever it disagrees with `inferred`.
        //
        // Original (#1965): only corrected inferred=Int, actual=non-Int (inference
        // defaults to Int but encoded term carries Unit/Datatype).
        //
        // Extended (#2570): also correct inferred=non-Int, actual=Int. This occurs
        // when the PureExpr annotation carries a MutRef/TypeParam sort but the
        // RustHorn borrow model decomposes the reference, leaving the encoded term
        // as Int. Without this, encode_closure_spec_method declares the UF with a
        // non-Int domain sort but passes an Int-sorted argument to safe_apply,
        // causing "sort mismatch in closure_spec:postcondition" errors for generic
        // DerefMut postconditions.
        let param_sorts: Vec<Sort> = std::iter::once(spec_receiver)
            .chain(args.iter())
            .enumerate()
            .map(|(i, expr)| {
                let inferred = self.infer_expr_sort_with_context(expr, prefix);
                let actual = self.solver.get_sort(all_terms[i]);
                if inferred == actual {
                    inferred
                } else {
                    actual
                }
            })
            .collect();
        let smt_name = Self::closure_spec_symbol(method, &param_sorts);
        let func_decl = self.get_or_declare_logic_func(&smt_name, &param_sorts, Sort::Bool);

        let context = format!("closure_spec:{method}");
        self.safe_apply(&context, &func_decl, &all_terms)
    }
}

#[cfg(test)]
mod tests;
