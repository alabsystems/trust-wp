// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Derived variable-name classification and formatting helpers.

/// Which derivation pattern was detected on a synthesized variable name.
/// (#2020 Slice 3)
///
/// Suffix checks take priority over prefix checks, matching the resolution
/// cascade order in `resolve_var_sort_candidate`. For names with both
/// a prefix and a suffix (e.g., `old_x_current_view`), the outermost suffix
/// wins. Inner `old_` / `final_` prefixes are handled separately by the
/// resolution path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DerivedKind {
    /// Has `_view` suffix (e.g., `x_view`, `x_current_view`, `final_x_view`).
    View,
    /// Has `_current` suffix (e.g., `x_current`, `old_x_current`).
    Current,
    /// Has `_final` suffix (e.g., `x_final`).
    Final,
    /// Has `_prime` suffix (e.g., `x_prime`).
    Prime,
    /// Has `old_` prefix but no known suffix (e.g., `old_x`).
    Old,
    /// Has `final_` prefix but no known suffix (e.g., `final_x`).
    ///
    /// This is primarily an intermediate form used while peeling or composing
    /// `final_{x}_view` names. It is intentionally not returned by
    /// [`classify_var_name`], which keeps the derived-name fence conservative
    /// for top-level source-name detection.
    FinalPrefix,
}

/// Classify a variable name as source or derived. (#2020 Slice 3)
///
/// Returns the outermost derivation kind, or `None` for source names
/// (direct variable names from MIR input expressions). Suffix checks
/// take priority over prefix checks, matching the resolution cascade
/// order.
pub(crate) fn classify_var_name(name: &str) -> Option<DerivedKind> {
    match DerivedKind::strip_from(name) {
        Some((DerivedKind::FinalPrefix, _)) | None => None,
        Some((kind, _)) => Some(kind),
    }
}

/// Returns `true` if `name` has a known synthesized suffix or prefix.
///
/// Convenience wrapper around [`classify_var_name`]. Prefer the richer
/// enum when caller-specific logic depends on which kind of derived name
/// was detected.
#[cfg(test)]
pub(crate) fn is_derived_var_name(name: &str) -> bool {
    classify_var_name(name).is_some()
}

impl DerivedKind {
    /// Construct a derived variable name from a base name.
    ///
    /// `DerivedKind::View.format_name("x")` → `"x_view"`,
    /// `DerivedKind::Old.format_name("x")` → `"old_x"`.
    pub(crate) fn format_name(self, base: &str) -> String {
        match self {
            Self::View => format!("{base}_view"),
            Self::Current => format!("{base}_current"),
            Self::Final => format!("{base}_final"),
            Self::Prime => format!("{base}_prime"),
            Self::Old => format!("old_{base}"),
            Self::FinalPrefix => format!("final_{base}"),
        }
    }

    /// Construct a nested derived name by applying each kind from inner to
    /// outer.
    ///
    /// `DerivedKind::format_chain("x", &[Current, Final])` →
    /// `"x_current_final"`,
    /// `DerivedKind::format_chain("x", &[FinalPrefix, View])` →
    /// `"final_x_view"`.
    pub(crate) fn format_chain(base: &str, chain: &[Self]) -> String {
        chain
            .iter()
            .fold(base.to_string(), |name, kind| kind.format_name(&name))
    }

    /// Extract the base name and derivation kind from a derived name.
    ///
    /// Returns `None` for source names. Suffix checks take priority
    /// over prefix checks, matching [`classify_var_name`].
    ///
    /// `DerivedKind::strip_from("x_view")` → `Some((View, "x"))`,
    /// `DerivedKind::strip_from("old_x")` → `Some((Old, "x"))`,
    /// `DerivedKind::strip_from("counter")` → `None`.
    pub(crate) fn strip_from(name: &str) -> Option<(Self, &str)> {
        if let Some(base) = name.strip_suffix("_view") {
            Some((Self::View, base))
        } else if let Some(base) = name.strip_suffix("_current") {
            Some((Self::Current, base))
        } else if let Some(base) = name.strip_suffix("_final") {
            Some((Self::Final, base))
        } else if let Some(base) = name.strip_suffix("_prime") {
            Some((Self::Prime, base))
        } else if let Some(base) = name.strip_prefix("old_") {
            Some((Self::Old, base))
        } else if let Some(base) = name.strip_prefix("final_") {
            Some((Self::FinalPrefix, base))
        } else {
            None
        }
    }

    /// Strip one leading `old_` derivation from `name`.
    ///
    /// This stays separate from [`DerivedKind::strip_from`]: that helper gives
    /// suffixes priority, so names like `old_x_current` classify as
    /// `(Current, "old_x")`. Old-prefix peeling must still produce
    /// `"x_current"` so the suffix cascade can continue resolving. (#2020)
    pub(crate) fn strip_old_prefix(name: &str) -> Option<&str> {
        name.strip_prefix("old_")
    }

    /// Strip an inner `final_` prefix from a `_view` chain while preserving
    /// any remaining suffixes on the base.
    ///
    /// `final_v_view` -> `v_view`
    /// `final_v_current_view` -> `v_current_view`
    /// `final_old_v_view` -> `old_v_view`
    ///
    /// This stays separate from [`DerivedKind::strip_from`]: suffix-priority
    /// parsing can only expose the outer `_view` layer, not the inner
    /// `final_` prefix that still needs to be peeled. (#2020)
    pub(crate) fn peel_final_view_prefix(name: &str) -> Option<String> {
        let (Self::View, base) = Self::strip_from(name)? else {
            return None;
        };
        let stripped = base.strip_prefix("final_")?;
        Some(Self::View.format_name(stripped))
    }

    /// Iterate over names produced by repeatedly peeling leading `old_`
    /// derivations.
    ///
    /// For example, `old_old_v_current` yields `old_v_current`, then
    /// `v_current`. This lets callers reuse the same derived-name model for
    /// mixed `old_` + suffix chains instead of open-coding repeated
    /// `strip_prefix("old_")` loops. [`DerivedKind::strip_from`] cannot drive
    /// this directly because it gives suffixes priority over the inner
    /// `old_` prefix. (#2020 Slice 3)
    pub(crate) fn peel_old_prefixes(name: &str) -> impl Iterator<Item = &str> {
        let mut next = name;
        std::iter::from_fn(move || {
            let stripped = Self::strip_old_prefix(next)?;
            next = stripped;
            Some(stripped)
        })
    }
}

#[cfg(test)]
mod tests {
    use ntest::timeout;

    use super::*;

    // ── classify_var_name ────────────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_view_suffix() {
        assert_eq!(classify_var_name("x_view"), Some(DerivedKind::View));
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_current_suffix() {
        assert_eq!(classify_var_name("x_current"), Some(DerivedKind::Current));
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_final_suffix() {
        assert_eq!(classify_var_name("x_final"), Some(DerivedKind::Final));
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_prime_suffix() {
        assert_eq!(classify_var_name("x_prime"), Some(DerivedKind::Prime));
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_old_prefix() {
        assert_eq!(classify_var_name("old_x"), Some(DerivedKind::Old));
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_source_name_returns_none() {
        assert_eq!(classify_var_name("counter"), None);
        assert_eq!(classify_var_name("x"), None);
        assert_eq!(classify_var_name("result"), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_final_prefix_returns_none() {
        // FinalPrefix is intentionally not returned by classify_var_name
        // to keep the derived-name fence conservative.
        assert_eq!(classify_var_name("final_x"), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_classify_var_name_suffix_priority_over_prefix() {
        // "old_x_current" has both old_ prefix and _current suffix.
        // Suffix takes priority per the cascade rules.
        assert_eq!(
            classify_var_name("old_x_current"),
            Some(DerivedKind::Current)
        );
        assert_eq!(classify_var_name("old_x_view"), Some(DerivedKind::View));
    }

    // ── is_derived_var_name ─────────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_is_derived_var_name_true_cases() {
        assert!(is_derived_var_name("x_view"));
        assert!(is_derived_var_name("x_current"));
        assert!(is_derived_var_name("x_final"));
        assert!(is_derived_var_name("x_prime"));
        assert!(is_derived_var_name("old_x"));
    }

    #[test]
    #[timeout(30000)]
    fn test_is_derived_var_name_false_cases() {
        assert!(!is_derived_var_name("counter"));
        assert!(!is_derived_var_name("x"));
        assert!(!is_derived_var_name("final_x")); // FinalPrefix is excluded
    }

    // ── DerivedKind::format_name ────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_format_name_all_kinds() {
        assert_eq!(DerivedKind::View.format_name("x"), "x_view");
        assert_eq!(DerivedKind::Current.format_name("x"), "x_current");
        assert_eq!(DerivedKind::Final.format_name("x"), "x_final");
        assert_eq!(DerivedKind::Prime.format_name("x"), "x_prime");
        assert_eq!(DerivedKind::Old.format_name("x"), "old_x");
        assert_eq!(DerivedKind::FinalPrefix.format_name("x"), "final_x");
    }

    #[test]
    #[timeout(30000)]
    fn test_format_name_empty_base() {
        assert_eq!(DerivedKind::View.format_name(""), "_view");
        assert_eq!(DerivedKind::Old.format_name(""), "old_");
    }

    // ── DerivedKind::format_chain ───────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_format_chain_single_kind() {
        assert_eq!(
            DerivedKind::format_chain("x", &[DerivedKind::Current]),
            "x_current"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_format_chain_multiple_kinds() {
        assert_eq!(
            DerivedKind::format_chain("x", &[DerivedKind::Current, DerivedKind::Final]),
            "x_current_final"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_format_chain_prefix_then_suffix() {
        assert_eq!(
            DerivedKind::format_chain("x", &[DerivedKind::FinalPrefix, DerivedKind::View]),
            "final_x_view"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_format_chain_empty_chain() {
        assert_eq!(DerivedKind::format_chain("x", &[]), "x");
    }

    // ── DerivedKind::strip_from ─────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_strip_from_view_suffix() {
        assert_eq!(
            DerivedKind::strip_from("x_view"),
            Some((DerivedKind::View, "x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_current_suffix() {
        assert_eq!(
            DerivedKind::strip_from("x_current"),
            Some((DerivedKind::Current, "x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_final_suffix() {
        assert_eq!(
            DerivedKind::strip_from("x_final"),
            Some((DerivedKind::Final, "x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_prime_suffix() {
        assert_eq!(
            DerivedKind::strip_from("x_prime"),
            Some((DerivedKind::Prime, "x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_old_prefix() {
        assert_eq!(
            DerivedKind::strip_from("old_x"),
            Some((DerivedKind::Old, "x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_final_prefix() {
        assert_eq!(
            DerivedKind::strip_from("final_x"),
            Some((DerivedKind::FinalPrefix, "x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_source_name_returns_none() {
        assert_eq!(DerivedKind::strip_from("counter"), None);
        assert_eq!(DerivedKind::strip_from("x"), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_suffix_priority_over_prefix() {
        // "old_x_view" should match _view suffix first, yielding base "old_x"
        assert_eq!(
            DerivedKind::strip_from("old_x_view"),
            Some((DerivedKind::View, "old_x"))
        );
        // "final_x_current" should match _current suffix first
        assert_eq!(
            DerivedKind::strip_from("final_x_current"),
            Some((DerivedKind::Current, "final_x"))
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_from_roundtrip_with_format_name() {
        let kinds = [
            DerivedKind::View,
            DerivedKind::Current,
            DerivedKind::Final,
            DerivedKind::Prime,
            DerivedKind::Old,
            DerivedKind::FinalPrefix,
        ];
        for kind in kinds {
            let formatted = kind.format_name("base_var");
            let (stripped_kind, stripped_base) =
                DerivedKind::strip_from(&formatted).expect("roundtrip should succeed");
            assert_eq!(stripped_kind, kind, "kind mismatch for {formatted}");
            assert_eq!(stripped_base, "base_var", "base mismatch for {formatted}");
        }
    }

    // ── DerivedKind::strip_old_prefix ───────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_strip_old_prefix_present() {
        assert_eq!(DerivedKind::strip_old_prefix("old_x"), Some("x"));
        assert_eq!(
            DerivedKind::strip_old_prefix("old_x_current"),
            Some("x_current")
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_strip_old_prefix_absent() {
        assert_eq!(DerivedKind::strip_old_prefix("x"), None);
        assert_eq!(DerivedKind::strip_old_prefix("x_view"), None);
        assert_eq!(DerivedKind::strip_old_prefix("final_x"), None);
    }

    // ── DerivedKind::peel_final_view_prefix ─────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_peel_final_view_prefix_basic() {
        assert_eq!(
            DerivedKind::peel_final_view_prefix("final_v_view"),
            Some("v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_final_view_prefix_with_current() {
        assert_eq!(
            DerivedKind::peel_final_view_prefix("final_v_current_view"),
            Some("v_current_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_final_view_prefix_with_old() {
        assert_eq!(
            DerivedKind::peel_final_view_prefix("final_old_v_view"),
            Some("old_v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_final_view_prefix_no_view_suffix_returns_none() {
        assert_eq!(DerivedKind::peel_final_view_prefix("final_v"), None);
        assert_eq!(DerivedKind::peel_final_view_prefix("final_v_current"), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_final_view_prefix_no_final_prefix_returns_none() {
        assert_eq!(DerivedKind::peel_final_view_prefix("v_view"), None);
        assert_eq!(DerivedKind::peel_final_view_prefix("old_v_view"), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_final_view_prefix_source_name_returns_none() {
        assert_eq!(DerivedKind::peel_final_view_prefix("counter"), None);
    }

    // ── DerivedKind::peel_old_prefixes ──────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_peel_old_prefixes_single() {
        let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_x").collect();
        assert_eq!(names, vec!["x"]);
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_old_prefixes_double() {
        let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_old_x").collect();
        assert_eq!(names, vec!["old_x", "x"]);
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_old_prefixes_triple() {
        let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_old_old_x").collect();
        assert_eq!(names, vec!["old_old_x", "old_x", "x"]);
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_old_prefixes_no_old_prefix() {
        let names: Vec<&str> = DerivedKind::peel_old_prefixes("x").collect();
        assert!(names.is_empty());
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_old_prefixes_with_suffix() {
        let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_old_v_current").collect();
        assert_eq!(names, vec!["old_v_current", "v_current"]);
    }

    #[test]
    #[timeout(30000)]
    fn test_peel_old_prefixes_empty_string() {
        let names: Vec<&str> = DerivedKind::peel_old_prefixes("").collect();
        assert!(names.is_empty());
    }
}
