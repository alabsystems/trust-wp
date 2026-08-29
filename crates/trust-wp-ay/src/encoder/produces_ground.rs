// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ay_dpll::api::Term;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ProducesGroundCall {
    pub(crate) from: Term,
    pub(crate) visited: Term,
    pub(crate) to: Term,
}

/// Ground transitivity call tracker with O(1) dedup and a cap to prevent
/// combinatorial explosion of SMT assertions at high call counts.
///
/// Below the cap, ground instances are emitted alongside the quantified axiom.
/// Above the cap, only the quantified axiom is relied upon. (#935)
#[derive(Clone)]
pub(crate) struct ProducesGroundCalls {
    /// Ordered list of observed calls (for iteration).
    calls: Vec<ProducesGroundCall>,
    /// Dedup set for O(1) membership check.
    seen: HashSet<ProducesGroundCall>,
}

/// Maximum number of ground calls per function symbol before falling back
/// to quantifier-only mode.
///
/// Reduced from 30 → 12 (#3313) → 8 (#2688) → 6 (#2671): ghost iterator
/// tests timeout because the combined produces ground instances plus
/// standard ground budget exceed solver capacity. At N=6 the cumulative
/// assertion count drops further while the quantified transitivity axiom
/// covers chains longer than the ground instances. Combined with the
/// lower 3-hop and 4-hop caps, this eliminates ghost iterator timeouts.
const TRUST_WP_PRODUCES_GROUND_CAP: usize = 6;

/// Maximum number of ground calls per function symbol before disabling
/// 4-hop transitivity instances, falling back to 2-hop + 3-hop only.
///
/// Reduced from 8 → 4 (#2688): the 4-hop loop is O(N³) per new call.
/// At N=8, each call emits 4×8³ = 2048 four-hop instances; at N=4 it
/// emits 4×4³ = 256 — an 8× reduction. Since the quantified transitivity
/// axiom handles 4+ hop chains and the 2-hop/3-hop ground instances
/// cover most practical verification needs, the lower cap eliminates
/// the dominant cost driver for iterator adapter timeouts.
const TRUST_WP_PRODUCES_FOUR_HOP_CAP: usize = 4;

/// Maximum number of ground calls per function symbol before disabling
/// 3-hop transitivity instances, falling back to 2-hop only. (#2671)
///
/// Reduced from 10 → 6 (#2688) → 4 (#2671): the 3-hop loop is O(N²)
/// per new call. At N=6, each call emits 3×6² = 108 three-hop instances;
/// at N=4 it emits 3×4² = 48 — a further 2× reduction. Ghost iterator
/// tests generate many produces calls from transitivity chains, and the
/// lower cap keeps ground instances within solver budget. The quantified
/// transitivity axiom handles 3+ hop chains.
const TRUST_WP_PRODUCES_THREE_HOP_CAP: usize = 4;

/// Maximum number of ground calls for adapter-typed produces functions
/// before falling back to quantifier-only mode. (#2688)
///
/// Iterator adapters like Map, Filter, FilterMap, and MapInv have opaque
/// `produces` definitions (no transparent rewrite at the driver level).
/// Ground transitivity instances are less valuable for these types because
/// the solver cannot learn concrete content from the abstract `produces`
/// predicate. A lower cap of 4 (vs 8 for concrete iterators) reduces
/// assertion volume ~4x while the quantified axiom provides coverage.
const TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP: usize = 4;

/// 3-hop cap for adapter-typed produces functions. (#2688)
///
/// Adapter produces functions get a lower 3-hop cap of 3 (vs 6 for
/// concrete iterators) because their abstract semantics provide less
/// return on multi-hop ground instances. The quantified transitivity
/// axiom handles chains beyond 2-hop.
const TRUST_WP_ADAPTER_THREE_HOP_CAP: usize = 3;

/// 4-hop cap for adapter-typed produces functions. (#2688)
///
/// Adapter types skip 4-hop entirely (cap of 2, effectively disabled
/// after the first two calls) since the O(N^3) cost is not justified
/// for abstract produces predicates.
const TRUST_WP_ADAPTER_FOUR_HOP_CAP: usize = 2;

/// Hex-encoded sort tag fragments that identify iterator adapter types in
/// produces function symbol names. These are the `encode_method_sort_tag`
/// outputs for the Uninterpreted/Datatype sort names used by Map, Filter,
/// FilterMap, and MapInv adapter carriers.
///
/// The produces function symbol includes the sort signature (e.g.,
/// `method_produces_3_u<hex>_s_u<hex>` or `method_produces_3_d<hex>_s_d<hex>`),
/// so substring matching on the hex-encoded type name suffices to detect
/// adapter-typed produces functions without requiring access to the original
/// sort objects.
///
/// Uses `iter::` prefix fragments (`697465723a3a`) to avoid false positives
/// from collection types like `HashMap` whose hex encoding would also
/// contain the bare `4d6170` ("Map") fragment. (#2688)
const ADAPTER_SORT_TAG_FRAGMENTS: &[&str] = &[
    // "iter::Map" → hex "697465723a3a4d6170" — catches all module-qualified
    // Map adapter paths (core::iter::Map, std::iter::Map, etc.)
    "697465723a3a4d6170",
    // "iter::Filter" → hex "697465723a3a46696c746572"
    "697465723a3a46696c746572",
    // "iter::MapInv" → hex "697465723a3a4d6170496e76"
    "697465723a3a4d6170496e76",
    // "MapInv" without iter:: prefix for creusot_std::MapInv path
    "4d6170496e76",
    // "iter::Enumerate" → hex "697465723a3a456e756d6572617465" (#2688)
    "697465723a3a456e756d6572617465",
    // "iter::Skip" → hex "697465723a3a536b6970" (#2688)
    "697465723a3a536b6970",
    // "iter::Take" → hex "697465723a3a54616b65" (#2688)
    "697465723a3a54616b65",
    // "iter::Zip" → hex "697465723a3a5a6970" (#2688)
    "697465723a3a5a6970",
    // "iter::Chain" → hex "697465723a3a436861696e" (#2688)
    "697465723a3a436861696e",
    // "iter::Fuse" → hex "697465723a3a46757365" (#2688)
    "697465723a3a46757365",
    // "iter::Cloned" → hex "697465723a3a436c6f6e6564" (#2688)
    "697465723a3a436c6f6e6564",
    // "iter::Copied" → hex "697465723a3a436f70696564" (#2688)
    "697465723a3a436f70696564",
    // "iter::Rev" → hex "697465723a3a526576" (#2688)
    "697465723a3a526576",
    // "iter::Peekable" → hex "697465723a3a5065656b61626c65" (#2688)
    "697465723a3a5065656b61626c65",
];

/// Check whether a produces function symbol name suggests an iterator
/// adapter type based on sort tag fragments in the symbol. (#2688)
///
/// Returns `true` for produces functions whose sort signature contains
/// any of the adapter type name hex encodings. This is a heuristic —
/// false positives (e.g., a user type named "Map") are safe because they
/// only result in tighter ground caps, not unsoundness.
pub(crate) fn is_adapter_produces_symbol(fn_symbol: &str) -> bool {
    // Only check symbols that start with "method_produces_"
    if !fn_symbol.starts_with("method_produces_") {
        return false;
    }
    // Skip the prefix "method_produces_N_" and check the sort signature
    // portion for adapter type hex fragments.
    // Filter out common false positives: "FMap" (46 4d 61 70) is a
    // collection type, not an iterator adapter. The "Filter" fragment
    // is long enough to avoid matching "FMap".
    ADAPTER_SORT_TAG_FRAGMENTS
        .iter()
        .any(|frag| fn_symbol.contains(frag))
}

impl Default for ProducesGroundCalls {
    fn default() -> Self {
        Self::new()
    }
}

impl ProducesGroundCalls {
    pub(super) fn new() -> Self {
        Self {
            calls: Vec::new(),
            seen: HashSet::new(),
        }
    }

    /// Insert a new call. Returns false if it was already present or if
    /// the hard storage cap has been reached.
    ///
    /// The `calls` Vec and `seen` HashSet stop growing once the overall
    /// ground cap is exceeded. Beyond the cap, ground instances are
    /// skipped (see `is_capped`), so there is no value in tracking
    /// additional calls — but without this limit the tracker's memory
    /// grows unboundedly for iterator-heavy functions. (#OOM)
    pub(super) fn insert(&mut self, call: ProducesGroundCall) -> bool {
        // Hard storage cap: stop accumulating calls once we're well past the
        // point where ground instantiation is disabled. 2× the overall cap
        // gives a margin for the adapter vs standard distinction while still
        // bounding memory.
        if self.calls.len() >= TRUST_WP_PRODUCES_GROUND_CAP * 2 {
            return false;
        }
        if self.seen.insert(call) {
            self.calls.push(call);
            true
        } else {
            false
        }
    }

    /// Whether the cap has been exceeded, meaning ground instances should be
    /// skipped in favor of the quantified axiom.
    pub(super) fn is_capped(&self) -> bool {
        self.calls.len() > TRUST_WP_PRODUCES_GROUND_CAP
    }

    /// Whether the cap has been exceeded for adapter-typed produces functions.
    ///
    /// Adapter types (Map, Filter, FilterMap, MapInv) have opaque produces
    /// definitions, so ground transitivity instances provide less value than
    /// for concrete iterator types. The adapter cap (`TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP`)
    /// is lower than the standard cap. (#2688)
    pub(super) fn is_adapter_capped(&self) -> bool {
        self.calls.len() > TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP
    }

    /// Whether four-hop ground transitivity should be disabled for this symbol.
    ///
    /// Above `TRUST_WP_PRODUCES_FOUR_HOP_CAP` calls, the O(N^3) four-hop loop dominates
    /// solver time without proportional benefit. Two-hop and three-hop ground
    /// instances plus the quantified axiom provide sufficient coverage. (#3313)
    pub(super) fn is_four_hop_disabled(&self) -> bool {
        self.calls.len() > TRUST_WP_PRODUCES_FOUR_HOP_CAP
    }

    /// Whether four-hop is disabled for adapter-typed produces functions.
    pub(super) fn is_adapter_four_hop_disabled(&self) -> bool {
        self.calls.len() > TRUST_WP_ADAPTER_FOUR_HOP_CAP
    }

    /// Whether three-hop ground transitivity should be disabled for this symbol.
    ///
    /// Above `TRUST_WP_PRODUCES_THREE_HOP_CAP` calls, the O(N^2) three-hop loop generates
    /// too many SMT assertions for iterator-heavy tests. Two-hop ground instances
    /// plus the quantified axiom provide sufficient coverage for longer chains.
    /// (#2688)
    pub(super) fn is_three_hop_disabled(&self) -> bool {
        self.calls.len() > TRUST_WP_PRODUCES_THREE_HOP_CAP
    }

    /// Whether three-hop is disabled for adapter-typed produces functions.
    pub(super) fn is_adapter_three_hop_disabled(&self) -> bool {
        self.calls.len() > TRUST_WP_ADAPTER_THREE_HOP_CAP
    }

    /// Returns the calls recorded *before* the last insert (i.e., all but the last).
    /// Panics if empty.
    pub(super) fn prior_calls(&self) -> &[ProducesGroundCall] {
        &self.calls[..self.calls.len() - 1]
    }

    /// All recorded calls.
    pub(super) fn all_calls(&self) -> &[ProducesGroundCall] {
        &self.calls
    }
}

#[cfg(test)]
mod tests {
    use ntest::timeout;

    use super::*;
    use crate::encoder::AYEncoder;

    /// Helper: create distinct `ProducesGroundCall` values using solver int constants.
    fn make_call(encoder: &mut AYEncoder, id: i64) -> ProducesGroundCall {
        // Use distinct integer constants so each call is unique in the HashSet.
        ProducesGroundCall {
            from: encoder.solver.int_const(id * 3),
            visited: encoder.solver.int_const(id * 3 + 1),
            to: encoder.solver.int_const(id * 3 + 2),
        }
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_insert_and_dedup() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        let c1 = make_call(&mut encoder, 0);
        assert!(tracker.insert(c1), "first insert should succeed");
        assert!(!tracker.insert(c1), "duplicate insert should return false");
        assert_eq!(
            tracker.all_calls().len(),
            1,
            "dedup should prevent duplicate"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_prior_calls_single_element() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        let c1 = make_call(&mut encoder, 0);
        tracker.insert(c1);
        assert_eq!(
            tracker.prior_calls().len(),
            0,
            "prior_calls with 1 element should return empty slice"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_prior_calls_two_elements() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        let c1 = make_call(&mut encoder, 0);
        let c2 = make_call(&mut encoder, 1);
        tracker.insert(c1);
        tracker.insert(c2);
        let prior = tracker.prior_calls();
        assert_eq!(
            prior.len(),
            1,
            "prior_calls with 2 elements should return 1"
        );
        assert_eq!(
            prior[0], c1,
            "prior_calls should return first inserted call"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_is_capped_at_boundary() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        // Insert exactly TRUST_WP_PRODUCES_GROUND_CAP calls.
        for i in 0..TRUST_WP_PRODUCES_GROUND_CAP {
            let id =
                i64::try_from(i).expect("TRUST_WP_PRODUCES_GROUND_CAP index should fit in i64");
            assert!(
                tracker.insert(make_call(&mut encoder, id)),
                "insert at index {i} should succeed"
            );
        }
        assert_eq!(
            tracker.all_calls().len(),
            TRUST_WP_PRODUCES_GROUND_CAP,
            "should hold exactly TRUST_WP_PRODUCES_GROUND_CAP calls"
        );
        assert!(
            !tracker.is_capped(),
            "at exactly {TRUST_WP_PRODUCES_GROUND_CAP} calls, should NOT be capped (> not >=)"
        );

        // Insert one more to exceed the cap.
        let cap_id = i64::try_from(TRUST_WP_PRODUCES_GROUND_CAP)
            .expect("TRUST_WP_PRODUCES_GROUND_CAP should fit in i64");
        assert!(
            tracker.insert(make_call(&mut encoder, cap_id)),
            "insert at cap+1 should succeed"
        );
        assert_eq!(
            tracker.all_calls().len(),
            TRUST_WP_PRODUCES_GROUND_CAP + 1,
            "should hold cap+1 calls after extra insert"
        );
        assert!(
            tracker.is_capped(),
            "at {} calls, should be capped",
            TRUST_WP_PRODUCES_GROUND_CAP + 1
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_cap_value_is_6() {
        // Pin the cap constant so changes require updating this test.
        assert_eq!(
            TRUST_WP_PRODUCES_GROUND_CAP, 6,
            "cap should be 6 per design (#2671, reduced from 8)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_four_hop_cap_value_is_4() {
        // Pin the four-hop cap constant so changes require updating this test.
        assert_eq!(
            TRUST_WP_PRODUCES_FOUR_HOP_CAP, 4,
            "four-hop cap should be 4 per design (#2688, reduced from 8)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_four_hop_disabled_at_boundary() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        // Insert exactly TRUST_WP_PRODUCES_FOUR_HOP_CAP calls.
        for i in 0..TRUST_WP_PRODUCES_FOUR_HOP_CAP {
            let id = i64::try_from(i).expect("index should fit in i64");
            assert!(
                tracker.insert(make_call(&mut encoder, id)),
                "insert at index {i} should succeed"
            );
        }
        assert!(
            !tracker.is_four_hop_disabled(),
            "at exactly {TRUST_WP_PRODUCES_FOUR_HOP_CAP} calls, four-hop should NOT be disabled (> not >=)"
        );

        // Insert one more to exceed the four-hop cap.
        let cap_id =
            i64::try_from(TRUST_WP_PRODUCES_FOUR_HOP_CAP).expect("index should fit in i64");
        assert!(
            tracker.insert(make_call(&mut encoder, cap_id)),
            "insert at cap+1 should succeed"
        );
        assert!(
            tracker.is_four_hop_disabled(),
            "at {} calls, four-hop should be disabled",
            TRUST_WP_PRODUCES_FOUR_HOP_CAP + 1
        );
        // But overall cap should NOT be reached yet.
        assert!(
            !tracker.is_capped(),
            "at {} calls, overall cap should NOT be reached (cap={})",
            TRUST_WP_PRODUCES_FOUR_HOP_CAP + 1,
            TRUST_WP_PRODUCES_GROUND_CAP,
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_prior_calls_at_cap() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        for i in 0..=TRUST_WP_PRODUCES_GROUND_CAP {
            let id =
                i64::try_from(i).expect("TRUST_WP_PRODUCES_GROUND_CAP index should fit in i64");
            tracker.insert(make_call(&mut encoder, id));
        }
        assert!(
            tracker.is_capped(),
            "tracker should be capped after inserting cap+1 calls"
        );
        // prior_calls should still work even above the cap.
        assert_eq!(
            tracker.prior_calls().len(),
            TRUST_WP_PRODUCES_GROUND_CAP,
            "prior_calls at cap+1 should return cap elements"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_three_hop_cap_value_is_4() {
        // Pin the three-hop cap constant so changes require updating this test.
        assert_eq!(
            TRUST_WP_PRODUCES_THREE_HOP_CAP, 4,
            "three-hop cap should be 4 per design (#2671, reduced from 6)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_produces_ground_calls_three_hop_disabled_at_boundary() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        // Insert exactly TRUST_WP_PRODUCES_THREE_HOP_CAP calls.
        for i in 0..TRUST_WP_PRODUCES_THREE_HOP_CAP {
            let id = i64::try_from(i).expect("index should fit in i64");
            assert!(
                tracker.insert(make_call(&mut encoder, id)),
                "insert at index {i} should succeed"
            );
        }
        assert!(
            !tracker.is_three_hop_disabled(),
            "at exactly {TRUST_WP_PRODUCES_THREE_HOP_CAP} calls, three-hop should NOT be disabled (> not >=)"
        );

        // Insert one more to exceed the three-hop cap.
        let cap_id =
            i64::try_from(TRUST_WP_PRODUCES_THREE_HOP_CAP).expect("index should fit in i64");
        assert!(
            tracker.insert(make_call(&mut encoder, cap_id)),
            "insert at cap+1 should succeed"
        );
        assert!(
            tracker.is_three_hop_disabled(),
            "at {} calls, three-hop should be disabled",
            TRUST_WP_PRODUCES_THREE_HOP_CAP + 1
        );
        // But overall cap should NOT be reached yet.
        assert!(
            !tracker.is_capped(),
            "at {} calls, overall cap should NOT be reached (cap={})",
            TRUST_WP_PRODUCES_THREE_HOP_CAP + 1,
            TRUST_WP_PRODUCES_GROUND_CAP,
        );
    }

    /// Verify the ordering of caps: three-hop <= overall, four-hop <= three-hop.
    #[test]
    #[timeout(30000)]
    fn test_produces_ground_cap_ordering() {
        assert!(
            TRUST_WP_PRODUCES_FOUR_HOP_CAP <= TRUST_WP_PRODUCES_THREE_HOP_CAP,
            "four-hop cap ({TRUST_WP_PRODUCES_FOUR_HOP_CAP}) must be <= three-hop cap ({TRUST_WP_PRODUCES_THREE_HOP_CAP})"
        );
        assert!(
            TRUST_WP_PRODUCES_THREE_HOP_CAP <= TRUST_WP_PRODUCES_GROUND_CAP,
            "three-hop cap ({TRUST_WP_PRODUCES_THREE_HOP_CAP}) must be <= overall cap ({TRUST_WP_PRODUCES_GROUND_CAP})"
        );
    }

    // --- Adapter-specific cap tests (#2688) ---

    #[test]
    #[timeout(30000)]
    fn test_adapter_produces_ground_cap_value() {
        assert_eq!(
            TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP, 4,
            "adapter overall cap should be 4 per design (#2688)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_adapter_three_hop_cap_value() {
        assert_eq!(
            TRUST_WP_ADAPTER_THREE_HOP_CAP, 3,
            "adapter three-hop cap should be 3 per design (#2688)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_adapter_four_hop_cap_value() {
        assert_eq!(
            TRUST_WP_ADAPTER_FOUR_HOP_CAP, 2,
            "adapter four-hop cap should be 2 per design (#2688)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_adapter_cap_ordering() {
        assert!(
            TRUST_WP_ADAPTER_FOUR_HOP_CAP < TRUST_WP_ADAPTER_THREE_HOP_CAP,
            "adapter four-hop cap must be less than adapter three-hop cap"
        );
        assert!(
            TRUST_WP_ADAPTER_THREE_HOP_CAP <= TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP,
            "adapter three-hop cap must be <= adapter overall cap"
        );
        assert!(
            TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP <= TRUST_WP_PRODUCES_GROUND_CAP,
            "adapter overall cap must be <= standard overall cap"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_adapter_capped_at_boundary() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        // Insert exactly TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP calls.
        for i in 0..TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP {
            let id = i64::try_from(i).expect("index should fit in i64");
            tracker.insert(make_call(&mut encoder, id));
        }
        assert!(
            !tracker.is_adapter_capped(),
            "at exactly {TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP} calls, adapter should NOT be capped"
        );

        // Insert one more to exceed the adapter cap.
        let cap_id =
            i64::try_from(TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP).expect("index should fit in i64");
        tracker.insert(make_call(&mut encoder, cap_id));
        assert!(
            tracker.is_adapter_capped(),
            "at {} calls, adapter should be capped",
            TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP + 1
        );
        // Standard cap should NOT be reached yet.
        assert!(
            !tracker.is_capped(),
            "standard cap should not be reached at {} calls",
            TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP + 1
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_adapter_three_hop_disabled_at_boundary() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        for i in 0..TRUST_WP_ADAPTER_THREE_HOP_CAP {
            let id = i64::try_from(i).expect("index should fit in i64");
            tracker.insert(make_call(&mut encoder, id));
        }
        assert!(
            !tracker.is_adapter_three_hop_disabled(),
            "at exactly {TRUST_WP_ADAPTER_THREE_HOP_CAP} calls, adapter three-hop should NOT be disabled"
        );

        let cap_id =
            i64::try_from(TRUST_WP_ADAPTER_THREE_HOP_CAP).expect("index should fit in i64");
        tracker.insert(make_call(&mut encoder, cap_id));
        assert!(
            tracker.is_adapter_three_hop_disabled(),
            "at {} calls, adapter three-hop should be disabled",
            TRUST_WP_ADAPTER_THREE_HOP_CAP + 1
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_adapter_four_hop_disabled_at_boundary() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();

        for i in 0..TRUST_WP_ADAPTER_FOUR_HOP_CAP {
            let id = i64::try_from(i).expect("index should fit in i64");
            tracker.insert(make_call(&mut encoder, id));
        }
        assert!(
            !tracker.is_adapter_four_hop_disabled(),
            "at exactly {TRUST_WP_ADAPTER_FOUR_HOP_CAP} calls, adapter four-hop should NOT be disabled"
        );

        let cap_id = i64::try_from(TRUST_WP_ADAPTER_FOUR_HOP_CAP).expect("index should fit in i64");
        tracker.insert(make_call(&mut encoder, cap_id));
        assert!(
            tracker.is_adapter_four_hop_disabled(),
            "at {} calls, adapter four-hop should be disabled",
            TRUST_WP_ADAPTER_FOUR_HOP_CAP + 1
        );
    }

    // --- is_adapter_produces_symbol tests (#2688) ---

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_core_iter_map() {
        // "core::iter::Map" → hex includes "697465723a3a4d6170" ("iter::Map")
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a4d6170_s_u636f72653a3a697465723a3a4d6170"
            ),
            "core::iter::Map produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_std_iter_map() {
        // "std::iter::Map" → hex includes "697465723a3a4d6170" ("iter::Map")
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u7374643a3a697465723a3a4d6170_s_u7374643a3a697465723a3a4d6170"
            ),
            "std::iter::Map produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_core_iter_filter() {
        // "core::iter::Filter" → hex includes "697465723a3a46696c746572" ("iter::Filter")
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a46696c746572_s_u636f72653a3a697465723a3a46696c746572"
            ),
            "core::iter::Filter produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_core_iter_filter_map() {
        // "core::iter::FilterMap" → hex includes "697465723a3a46696c7465724d6170"
        // which starts with "697465723a3a46696c746572" ("iter::Filter") fragment
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a46696c7465724d6170_s_u636f72653a3a697465723a3a46696c7465724d6170"
            ),
            "core::iter::FilterMap produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_map_inv() {
        // "trust_wp_std::std::iter::MapInv" → hex includes "697465723a3a4d6170496e76"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u73756e6465725f7374643a3a7374643a3a697465723a3a4d6170496e76_s_u73756e6465725f7374643a3a7374643a3a697465723a3a4d6170496e76"
            ),
            "MapInv produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_creusot_map_inv() {
        // "creusot_std::MapInv" → hex includes "4d6170496e76" (bare MapInv fragment)
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u63726575736f745f7374643a3a4d6170496e76_s_u63726575736f745f7374643a3a4d6170496e76"
            ),
            "creusot_std::MapInv produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_non_adapter_int() {
        assert!(
            !is_adapter_produces_symbol("method_produces_3_i_s_i"),
            "Int-sorted produces symbol should NOT be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_non_adapter_hashmap() {
        // "HashMap" → hex "486173684d6170". Does NOT contain "iter::Map"
        // fragment "697465723a3a4d6170", so should NOT be detected.
        assert!(
            !is_adapter_produces_symbol("method_produces_3_u486173684d6170_s_u486173684d6170"),
            "HashMap produces symbol should NOT be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_non_produces() {
        assert!(
            !is_adapter_produces_symbol("method_completed_1_u697465723a3a4d6170"),
            "Non-produces method symbol should NOT be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_empty_string() {
        assert!(
            !is_adapter_produces_symbol(""),
            "Empty string should NOT be detected as adapter"
        );
    }

    // --- Additional adapter type detection tests (#2688) ---

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_enumerate() {
        // "core::iter::adapters::enumerate::Enumerate" contains "iter::Enumerate"
        // → hex includes "697465723a3a456e756d6572617465"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a456e756d6572617465_s_u636f72653a3a697465723a3a456e756d6572617465"
            ),
            "core::iter::Enumerate produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_skip() {
        // "core::iter::adapters::skip::Skip" contains "iter::Skip"
        // → hex includes "697465723a3a536b6970"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a536b6970_s_u636f72653a3a697465723a3a536b6970"
            ),
            "core::iter::Skip produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_take() {
        // "core::iter::adapters::take::Take" contains "iter::Take"
        // → hex includes "697465723a3a54616b65"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a54616b65_s_u636f72653a3a697465723a3a54616b65"
            ),
            "core::iter::Take produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_zip() {
        // "core::iter::adapters::zip::Zip" contains "iter::Zip"
        // → hex includes "697465723a3a5a6970"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a5a6970_s_u636f72653a3a697465723a3a5a6970"
            ),
            "core::iter::Zip produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_chain() {
        // "core::iter::adapters::chain::Chain" contains "iter::Chain"
        // → hex includes "697465723a3a436861696e"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a436861696e_s_u636f72653a3a697465723a3a436861696e"
            ),
            "core::iter::Chain produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_fuse() {
        // "core::iter::adapters::fuse::Fuse" contains "iter::Fuse"
        // → hex includes "697465723a3a46757365"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a46757365_s_u636f72653a3a697465723a3a46757365"
            ),
            "core::iter::Fuse produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_cloned() {
        // "core::iter::adapters::cloned::Cloned" contains "iter::Cloned"
        // → hex includes "697465723a3a436c6f6e6564"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a436c6f6e6564_s_u636f72653a3a697465723a3a436c6f6e6564"
            ),
            "core::iter::Cloned produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_copied() {
        // "core::iter::adapters::copied::Copied" contains "iter::Copied"
        // → hex includes "697465723a3a436f70696564"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a436f70696564_s_u636f72653a3a697465723a3a436f70696564"
            ),
            "core::iter::Copied produces symbol should be detected as adapter"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_rev() {
        // "core::iter::adapters::rev::Rev" contains "iter::Rev"
        // → hex includes "697465723a3a526576"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a526576_s_u636f72653a3a697465723a3a526576"
            ),
            "core::iter::Rev produces symbol should be detected as adapter"
        );
    }

    /// Inserting 20 calls into the tracker only stores up to the hard storage
    /// cap (`TRUST_WP_PRODUCES_GROUND_CAP * 2 = 12`). Beyond that, `insert()` returns
    /// false and the Vec/HashSet stop growing. (#2709)
    #[test]
    #[timeout(30000)]
    fn test_hard_storage_cap_bounds_vec_and_hashset_at_12() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();
        let hard_cap = TRUST_WP_PRODUCES_GROUND_CAP * 2; // 12

        // Insert 20 unique calls — only the first `hard_cap` should be stored.
        let mut accepted = 0usize;
        for i in 0..20 {
            let id = i64::try_from(i).expect("index fits in i64");
            if tracker.insert(make_call(&mut encoder, id)) {
                accepted += 1;
            }
        }

        assert_eq!(
            tracker.all_calls().len(),
            hard_cap,
            "Vec should hold exactly {hard_cap} entries, not grow to 20"
        );
        assert_eq!(
            accepted, hard_cap,
            "only {hard_cap} inserts should be accepted"
        );
        // Confirm the rejected inserts were truly rejected (not just dedup).
        let rejected_call = make_call(&mut encoder, 19);
        assert!(
            !tracker.all_calls().contains(&rejected_call),
            "call 19 (beyond hard cap) must not be in the tracker"
        );
    }

    /// Simulate an iterator adapter chain scenario: multiple distinct trackers
    /// (one per adapter type) each hit the hard storage cap independently.
    /// No individual tracker grows beyond `TRUST_WP_PRODUCES_GROUND_CAP * 2`. (#2709)
    #[test]
    #[timeout(30000)]
    fn test_adapter_chain_trackers_bounded_independently() {
        let mut encoder = AYEncoder::new();
        let hard_cap = TRUST_WP_PRODUCES_GROUND_CAP * 2;
        let adapter_count = 5; // e.g., map().filter().enumerate().take().zip()

        let mut trackers: Vec<ProducesGroundCalls> = (0..adapter_count)
            .map(|_| ProducesGroundCalls::new())
            .collect();

        // Push 50 calls into each tracker (simulating heavy iteration).
        for (t_idx, tracker) in trackers.iter_mut().enumerate() {
            for call_idx in 0..50 {
                let id = i64::try_from(t_idx * 1000 + call_idx).expect("index fits in i64");
                tracker.insert(make_call(&mut encoder, id));
            }
        }

        for (t_idx, tracker) in trackers.iter().enumerate() {
            assert_eq!(
                tracker.all_calls().len(),
                hard_cap,
                "tracker {t_idx} should be bounded at {hard_cap}, not grow to 50"
            );
            assert!(tracker.is_capped(), "tracker {t_idx} should report capped");
        }

        // Total memory across all trackers is bounded: adapter_count * hard_cap.
        let total_stored: usize = trackers.iter().map(|t| t.all_calls().len()).sum();
        assert_eq!(
            total_stored,
            adapter_count * hard_cap,
            "total stored calls across {adapter_count} trackers should be exactly {}",
            adapter_count * hard_cap
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_is_adapter_produces_symbol_peekable() {
        // "core::iter::adapters::peekable::Peekable" contains "iter::Peekable"
        // → hex includes "697465723a3a5065656b61626c65"
        assert!(
            is_adapter_produces_symbol(
                "method_produces_3_u636f72653a3a697465723a3a5065656b61626c65_s_u636f72653a3a697465723a3a5065656b61626c65"
            ),
            "core::iter::Peekable produces symbol should be detected as adapter"
        );
    }

    // --- Hard storage cap tests (#2709) ---

    /// Inserting 20 calls should only store TRUST_WP_PRODUCES_GROUND_CAP * 2 = 12
    /// entries. Beyond the hard storage cap, `insert()` returns false and
    /// neither `calls` nor `seen` grow. This prevents unbounded memory
    /// growth in iterator-heavy functions.
    #[test]
    #[timeout(30000)]
    fn test_hard_storage_cap_limits_to_12_entries() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();
        let hard_cap = TRUST_WP_PRODUCES_GROUND_CAP * 2; // 12

        // Insert 20 unique calls — only the first 12 should be stored.
        for i in 0..20 {
            let call = make_call(&mut encoder, i);
            let inserted = tracker.insert(call);
            if (i as usize) < hard_cap {
                assert!(
                    inserted,
                    "insert at index {i} should succeed (below hard cap {hard_cap})"
                );
            } else {
                assert!(
                    !inserted,
                    "insert at index {i} should return false (at/above hard cap {hard_cap})"
                );
            }
        }

        assert_eq!(
            tracker.all_calls().len(),
            hard_cap,
            "tracker should store exactly {hard_cap} calls, not 20"
        );
        // Verify the hard cap constant is what we expect.
        assert_eq!(
            hard_cap, 12,
            "hard cap should be TRUST_WP_PRODUCES_GROUND_CAP * 2 = 12"
        );
    }

    /// Verify that the hard storage cap value (TRUST_WP_PRODUCES_GROUND_CAP * 2)
    /// is pinned so changes require updating this test.
    #[test]
    #[timeout(30000)]
    fn test_hard_storage_cap_value_is_twice_ground_cap() {
        assert_eq!(
            TRUST_WP_PRODUCES_GROUND_CAP * 2,
            12,
            "hard storage cap should be 2 * TRUST_WP_PRODUCES_GROUND_CAP = 12"
        );
    }

    /// Simulate an iterator adapter chain pattern: many calls arrive but
    /// the tracker's storage is bounded. After the hard cap, both the
    /// overall cap and adapter cap are exceeded, and no further storage
    /// occurs. This models the real-world scenario from #2709 where
    /// iterator adapter chains (Map, Filter, etc.) generate many produces
    /// calls that previously caused unbounded memory growth.
    #[test]
    #[timeout(30000)]
    fn test_adapter_chain_does_not_grow_tracker_beyond_cap() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();
        let hard_cap = TRUST_WP_PRODUCES_GROUND_CAP * 2; // 12

        // Simulate a chain of 50 adapter produces calls (e.g., from
        // Map→Filter→MapInv→Enumerate→... chains in iterator-heavy code).
        let mut accepted = 0usize;
        let mut rejected = 0usize;
        for i in 0..50 {
            if tracker.insert(make_call(&mut encoder, i)) {
                accepted += 1;
            } else {
                rejected += 1;
            }
        }

        assert_eq!(
            accepted, hard_cap,
            "exactly {hard_cap} calls should be accepted"
        );
        assert_eq!(
            rejected,
            50 - hard_cap,
            "remaining calls should be rejected"
        );
        assert_eq!(
            tracker.all_calls().len(),
            hard_cap,
            "tracker storage should be bounded at {hard_cap}"
        );

        // All the cap predicates should be true at this count.
        assert!(
            tracker.is_capped(),
            "standard cap should be exceeded at {hard_cap} calls (cap={})",
            TRUST_WP_PRODUCES_GROUND_CAP
        );
        assert!(
            tracker.is_adapter_capped(),
            "adapter cap should be exceeded at {hard_cap} calls (cap={})",
            TRUST_WP_ADAPTER_PRODUCES_GROUND_CAP
        );
        assert!(
            tracker.is_four_hop_disabled(),
            "four-hop should be disabled at {hard_cap} calls"
        );
        assert!(
            tracker.is_three_hop_disabled(),
            "three-hop should be disabled at {hard_cap} calls"
        );
        assert!(
            tracker.is_adapter_four_hop_disabled(),
            "adapter four-hop should be disabled at {hard_cap} calls"
        );
        assert!(
            tracker.is_adapter_three_hop_disabled(),
            "adapter three-hop should be disabled at {hard_cap} calls"
        );
    }

    /// Verify that duplicate inserts within the cap do not count toward
    /// the hard storage limit. Dedup via the HashSet and the hard storage
    /// cap are independent mechanisms.
    #[test]
    #[timeout(30000)]
    fn test_hard_storage_cap_unaffected_by_duplicates() {
        let mut encoder = AYEncoder::new();
        let mut tracker = ProducesGroundCalls::new();
        let hard_cap = TRUST_WP_PRODUCES_GROUND_CAP * 2; // 12

        // Insert 6 unique calls, each duplicated 3 times → 24 insert attempts.
        // Only 6 unique entries should be stored.
        for i in 0..6 {
            let call = make_call(&mut encoder, i);
            for _ in 0..3 {
                tracker.insert(call);
            }
        }
        assert_eq!(
            tracker.all_calls().len(),
            6,
            "only 6 unique calls should be stored despite 18 insert attempts"
        );

        // Now fill up to the hard cap with 6 more unique calls.
        for i in 6..12 {
            assert!(
                tracker.insert(make_call(&mut encoder, i)),
                "insert at index {i} should succeed (below hard cap)"
            );
        }
        assert_eq!(
            tracker.all_calls().len(),
            hard_cap,
            "tracker should be at hard cap after 12 unique inserts"
        );

        // One more unique call should be rejected.
        assert!(
            !tracker.insert(make_call(&mut encoder, 12)),
            "insert beyond hard cap should return false"
        );
        assert_eq!(
            tracker.all_calls().len(),
            hard_cap,
            "tracker should not grow beyond hard cap"
        );
    }
}
