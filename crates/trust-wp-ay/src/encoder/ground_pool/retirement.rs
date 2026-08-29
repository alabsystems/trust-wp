// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Staged retirement of eagerly-grounded FMap pool families (CAP-80).
//!
//! The FMap ground pool (`assert_fmap_ground_instances`) eagerly asserts
//! ground consequences of the quantified FMap axioms because ay-dpll's
//! single-round E-matching historically could not be relied on to instantiate
//! them. ay HEAD now *decides* a narrow quantifier fragment (rank 9:
//! pointwise-materializable UF definitions — head applied to exactly the
//! distinct binders, f-free interpreted-pure rhs/guards). Families whose
//! quantified axiom falls inside that fragment are redundant as ground copies
//! and can be demoted to plain quantifier passthrough.
//!
//! This module is the single source of truth for that classification and for
//! the staged demotion decision. The classification is *honest against ay
//! HEAD*, not shape-guessed:
//!
//! - The ONLY binder-exact FMap family is len non-negativity
//!   (`forall m. fmap_len(m) >= 0`): UF head applied to exactly the binder,
//!   interpreted-pure rhs. Direct evidence ay discharges it without the pool:
//!   `tests/coverage_gaps/fmap_axiom_tests.rs::fmap_len_nonneg` asserts the
//!   axioms only (no pool entries) and gets Unsat.
//! - `contains(insert(m,k,v),k)`, `lookup(insert(m,k,v),k)=v`, and the merge
//!   families have COMPOSITE heads (mixed-head) — outside the fragment, KEEP.
//! - insert-len and the insert×contains / insert×lookup frame cross-products
//!   relate the same symbol at two receivers (recursive frame) — KEEP.
//!
//! CAUTION (do not "upgrade" by shape alone): the FMap binder sort is
//! `Sort::Uninterpreted("FMap")`, which ay's bool-predicate certificate leg
//! explicitly excludes (empty-domain honesty, mbqi.rs). Any future demotion of
//! an FMap-sort-binding axiom needs an ay-side extension or a sort-encoding
//! change first, plus fresh driver-level A/B evidence.
//!
//! # Soundness
//!
//! Every pool instance is a ground consequence of an already-asserted
//! universal, so skipping a family can only remove redundant facts: Unsat can
//! only degrade to Unknown (acceptable), never invert; Sat is unaffected
//! because the universal still stands and ay never mints Sat without a
//! verified model over it. The demotion decision is fail-closed on BOTH
//! inputs: the family is retained unless the retirement stage is enabled AND
//! the quantified axiom was actually asserted for this solve (see
//! [`FmapQuantifiedCoverage`]).
//!
//! # Ordering doc-pin
//!
//! The coverage flags are only valid because `assert_fmap_axioms` runs before
//! every ground-pool flush (`solve_helpers.rs` asserts standard axioms before
//! `assert_standard_ground_instances`; the unscoped `check_sat` flush happens
//! after encoding and axiom assertion). Direct encoder users who never call
//! `assert_fmap_axioms` leave coverage `false` and keep the pool (fail-closed).
//! A future reordering that flushes before axiom assertion would silently
//! disable the demotion — still sound, but it would defeat the feature; keep
//! the axioms-before-flush ordering.

use std::sync::OnceLock;

/// Env var selecting the retirement stage. Unset or unparseable degrades to
/// stage 0 (legacy keep-everything) — no silent clamp of bad values to an
/// aggressive stage.
pub(crate) const TRUST_WP_GROUND_POOL_RETIREMENT_STAGE_ENV: &str =
    "TRUST_WP_GROUND_POOL_RETIREMENT_STAGE";

/// Cached process-wide retirement stage (OnceLock read-through, mirroring
/// `verify::profile::is_profile_enabled`). Tests must NOT toggle the env var
/// (racy under parallel tests); they use the encoder-level override or the
/// pure functions below.
static RETIREMENT_STAGE: OnceLock<u8> = OnceLock::new();

/// Classification of an FMap ground-pool family against ay HEAD's decided
/// quantifier fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PoolFamilyClass {
    /// The quantified axiom has a UF head applied to exactly the distinct
    /// binders with an f-free interpreted-pure rhs — inside ay's decided
    /// rank-9 fragment. Eligible for demotion to quantifier passthrough.
    BinderExactPassThrough,
    /// The quantified axiom's head is composite (e.g. `contains(insert(..),k)`)
    /// or has a ground receiver — outside the decided fragment. Keep grounding.
    MixedHead,
    /// The quantified axiom relates the same symbol at two receivers (frame /
    /// recursive shape) — outside the decided fragment. Keep grounding.
    RecursiveFrame,
}

/// The sequential code regions of `assert_fmap_ground_instances`, named so the
/// classification is data, not comments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FmapGroundFamily {
    /// `contains(insert(m,k,v),k) = true` per insert entry.
    InsertContains,
    /// `lookup(insert(m,k,v),k) = v` (+ payload projections) per insert entry.
    InsertLookup,
    /// `len(insert(m,k,v)) = ite(contains(m,k), len(m), len(m)+1)`.
    InsertLen,
    /// insert × contains frame cross-product.
    InsertContainsFrame,
    /// insert × lookup frame cross-product.
    InsertLookupFrame,
    /// `len(m) >= 0` per observed `fmap_len` entry.
    LenNonneg,
    /// merge × contains (+ lookup left/right) cross-product.
    MergeContains,
}

/// Static classification of each family. See the module docs for the honest
/// mapping against ay HEAD; only `LenNonneg` is binder-exact.
pub(crate) fn classify(family: FmapGroundFamily) -> PoolFamilyClass {
    match family {
        FmapGroundFamily::LenNonneg => PoolFamilyClass::BinderExactPassThrough,
        FmapGroundFamily::InsertContains
        | FmapGroundFamily::InsertLookup
        | FmapGroundFamily::MergeContains => PoolFamilyClass::MixedHead,
        FmapGroundFamily::InsertLen
        | FmapGroundFamily::InsertContainsFrame
        | FmapGroundFamily::InsertLookupFrame => PoolFamilyClass::RecursiveFrame,
    }
}

/// Pure demotion decision — fail-closed on both flags.
///
/// A family is demoted (its ground instances skipped, leaving the quantified
/// axiom as the sole semantic source) only when ALL of:
/// - the retirement stage is enabled (`stage >= 1`),
/// - the corresponding quantified universal was actually asserted for this
///   solve (`quantified_axiom_asserted`), and
/// - the family is inside ay's decided fragment (`BinderExactPassThrough`).
pub(crate) fn family_demoted(
    class: PoolFamilyClass,
    quantified_axiom_asserted: bool,
    stage: u8,
) -> bool {
    stage >= 1 && quantified_axiom_asserted && class == PoolFamilyClass::BinderExactPassThrough
}

/// Pure stage parser: checked `parse::<u8>()`; unset, empty, or unparseable
/// (including out-of-range like `"256"` or negatives) degrades to the
/// conservative stage 0. Exposed separately from the OnceLock wrapper so tests
/// can exercise it without touching process env.
pub(crate) fn parse_retirement_stage(raw: Option<&str>) -> u8 {
    raw.and_then(|value| value.trim().parse::<u8>().ok())
        .unwrap_or(0)
}

/// Process-wide retirement stage from `TRUST_WP_GROUND_POOL_RETIREMENT_STAGE`,
/// read once. Default (unset) is stage 0 = legacy keep-everything; the flip to
/// stage 1 is gated on the driver-level creusot-compat A/B (stage 0 vs 1).
pub(crate) fn retirement_stage_from_env() -> u8 {
    *RETIREMENT_STAGE.get_or_init(|| {
        parse_retirement_stage(
            std::env::var(TRUST_WP_GROUND_POOL_RETIREMENT_STAGE_ENV)
                .ok()
                .as_deref(),
        )
    })
}

/// Per-solve record of which quantified FMap universals `assert_fmap_axioms`
/// actually asserted. Lives on `AYEncoder`; defaults to all-`false`
/// (fail-closed: the ground pool is retained whenever a universal was NOT
/// asserted — `Logic::All` proxy mode, non-Int legacy insert signature,
/// missing `fmap_insert` decl, or direct encoder users that never call
/// `assert_fmap_axioms`).
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct FmapQuantifiedCoverage {
    /// `forall m. fmap_len(m) >= 0` was asserted (only in non-proxy len mode
    /// with a live `fmap_len` decl). The stage-1 gating input.
    pub(crate) len_nonneg: bool,
    /// Insert direct + frame universals were asserted (contains AND lookup
    /// legs). Recorded for the stage-2 A/B; NOT consulted by any gate yet.
    /// Any future gate must re-audit exactly which universals this implies.
    pub(crate) insert_semantics: bool,
    /// Merge contains/lookup universals were asserted (contains AND lookup
    /// legs). Recorded only; NOT consulted by any gate yet.
    pub(crate) merge_semantics: bool,
}

impl super::super::AYEncoder {
    /// Effective ground-pool retirement stage for this encoder: the test-only
    /// override wins, then the process-wide env flag, default stage 0.
    pub(crate) fn ground_pool_retirement_stage(&self) -> u8 {
        self.retirement_stage_override
            .unwrap_or_else(retirement_stage_from_env)
    }

    /// Test-only stage override (mirrors `GroundTermPool::per_slice_budget_override`)
    /// so tests avoid racing on the process-wide OnceLock env cache.
    #[cfg(test)]
    pub(crate) fn set_retirement_stage_override_for_test(&mut self, stage: Option<u8>) {
        self.retirement_stage_override = stage;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL_FAMILIES: [FmapGroundFamily; 7] = [
        FmapGroundFamily::InsertContains,
        FmapGroundFamily::InsertLookup,
        FmapGroundFamily::InsertLen,
        FmapGroundFamily::InsertContainsFrame,
        FmapGroundFamily::InsertLookupFrame,
        FmapGroundFamily::LenNonneg,
        FmapGroundFamily::MergeContains,
    ];

    #[test]
    fn only_len_nonneg_classifies_binder_exact() {
        for family in ALL_FAMILIES {
            let class = classify(family);
            if family == FmapGroundFamily::LenNonneg {
                assert_eq!(
                    class,
                    PoolFamilyClass::BinderExactPassThrough,
                    "len-nonneg is the single binder-exact family"
                );
            } else {
                assert_ne!(
                    class,
                    PoolFamilyClass::BinderExactPassThrough,
                    "{family:?} must stay eagerly grounded (mixed-head / recursive frame)"
                );
            }
        }
    }

    #[test]
    fn stage_zero_never_demotes() {
        for class in [
            PoolFamilyClass::BinderExactPassThrough,
            PoolFamilyClass::MixedHead,
            PoolFamilyClass::RecursiveFrame,
        ] {
            for covered in [false, true] {
                assert!(
                    !family_demoted(class, covered, 0),
                    "stage 0 is legacy keep-everything ({class:?}, covered={covered})"
                );
            }
        }
    }

    #[test]
    fn stage_one_demotes_only_covered_binder_exact() {
        assert!(family_demoted(
            PoolFamilyClass::BinderExactPassThrough,
            true,
            1
        ));
        // Fail-closed: no coverage → no demotion, even at aggressive stages.
        assert!(!family_demoted(
            PoolFamilyClass::BinderExactPassThrough,
            false,
            1
        ));
        assert!(!family_demoted(
            PoolFamilyClass::BinderExactPassThrough,
            false,
            2
        ));
        // Outside the decided fragment: never demoted regardless of stage.
        assert!(!family_demoted(PoolFamilyClass::MixedHead, true, 1));
        assert!(!family_demoted(PoolFamilyClass::RecursiveFrame, true, 1));
        assert!(!family_demoted(PoolFamilyClass::MixedHead, true, u8::MAX));
        assert!(!family_demoted(
            PoolFamilyClass::RecursiveFrame,
            true,
            u8::MAX
        ));
    }

    #[test]
    fn stage_two_keeps_binder_exact_demotion() {
        // Stage 2 (insert-direct candidates) is a superset switch: the
        // stage-1 demotion stays active.
        assert!(family_demoted(
            PoolFamilyClass::BinderExactPassThrough,
            true,
            2
        ));
    }

    #[test]
    fn parse_stage_degrades_to_conservative_zero() {
        assert_eq!(parse_retirement_stage(None), 0, "unset → stage 0");
        assert_eq!(parse_retirement_stage(Some("")), 0, "empty → stage 0");
        assert_eq!(
            parse_retirement_stage(Some("banana")),
            0,
            "unparseable → stage 0"
        );
        assert_eq!(
            parse_retirement_stage(Some("256")),
            0,
            "u8 overflow → stage 0 (checked parse, no clamp)"
        );
        assert_eq!(
            parse_retirement_stage(Some("-1")),
            0,
            "negative → stage 0 (checked parse, no wrap)"
        );
        assert_eq!(parse_retirement_stage(Some("0")), 0);
        assert_eq!(parse_retirement_stage(Some("1")), 1);
        assert_eq!(parse_retirement_stage(Some(" 1 ")), 1, "whitespace trimmed");
        assert_eq!(parse_retirement_stage(Some("2")), 2);
    }
}
