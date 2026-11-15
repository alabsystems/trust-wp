// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Projected final-value pin targets (#prophecy-slots, Fix B M5).
//!
//! ## What this type exists for
//!
//! The RustHorn `final_values` lane pins a prophecy by NAME: the key `"x"` (or
//! `"x.0"`, the tuple lane landed for `drop_pair`/`swap_borrows`) selects a
//! `&mut` PARAMETER, and the encoder asserts `x_final == <value at return>`.
//! That lane cannot address a `&mut` that lives *inside an enum payload*: the
//! payload has no name of its own, only a projection out of a carrier
//! (`Some(r)`, `Some((first, rem))`), and its expiry is not the function's
//! return — it is a point inside the CALLER's body.
//!
//! [`FinalPinTarget`] is the addressing scheme for that case, and
//! [`ProjectedFinalPin`] is one pin: *"at this proven death point, the prophecy
//! reached by walking `path` out of `root` equals `value`"*.
//!
//! ## The variant guard is part of the address, not decoration
//!
//! A [`PinStep::Variant`] step contributes BOTH a projection and a guard. An
//! unguarded pin on a `None`-branch payload is a fact about a term that denotes
//! nothing — a fabricated premise. Every consumer must emit
//! `is-<ctor>(root) ==> <pin>` for each variant step it walks through, matching
//! the in-house idiom (`emit_resolve_assertions`'s `implies(gate, eq)` and the
//! payload-getter bridges).
//!
//! ## Fail-closed contract for consumers
//!
//! A pin is a PREMISE. Producing one at an unproven death point is a
//! false-accept factory, so the producer side owns a disarm-on-uncertainty
//! discipline (see the driver's `projected_expiry` module) and the consumer
//! side must REFUSE — emit nothing — whenever the walk cannot be completed
//! exactly:
//!
//! * a path step that does not resolve to a native selector;
//! * a reached term that is not a real `MutRef` carrier (pinning `^` on a
//!   non-carrier is precisely the collapse Fix A refuses);
//! * a variant step whose tester cannot be built.
//!
//! Refusing only WEAKENS the premise set, so it is always the safe direction.

use crate::formula::{ExprSort, PureExpr};

/// One step of a [`FinalPinTarget`] path.
///
/// Steps are applied left to right starting from the root term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PinStep {
    /// Tuple element or struct field `i` — projected with the positional
    /// getter `__trust_wp_tuple_get_i`, which resolves to the native field
    /// selector when the receiver is a declared struct/tuple datatype.
    Field(usize),
    /// Enum variant payload. Contributes the guard `is-<ctor>(receiver)` AND
    /// the projection of field `field` of that constructor.
    ///
    /// `ctor` is the SHORT constructor name as it appears in the source
    /// (`"Some"`, `"Ok"`); consumers resolve it against the receiver's declared
    /// datatype, which may spell it `<family>__Some`.
    Variant { ctor: String, field: usize },
}

/// Where a projected final value lives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalPinTarget {
    /// Today's by-name lane, byte-identical in meaning to a `final_values`
    /// entry. Present so the two lanes share one vocabulary; the encoder still
    /// routes plain locals through `bind_single_final_value`.
    Local(String),
    /// A carrier reached by projecting out of `root`.
    Projection {
        /// Root variable name (a declared symbol: a call result, a local).
        root: String,
        /// Optional sort annotation for the root symbol.
        root_sort: Option<ExprSort>,
        /// Projection steps from the root to the carrier.
        path: Vec<PinStep>,
    },
}

impl FinalPinTarget {
    /// The root symbol name this target is addressed from.
    #[must_use]
    pub fn root_name(&self) -> &str {
        match self {
            FinalPinTarget::Local(name) => name,
            FinalPinTarget::Projection { root, .. } => root,
        }
    }

    /// Path steps (empty for the by-name lane).
    #[must_use]
    pub fn steps(&self) -> &[PinStep] {
        match self {
            FinalPinTarget::Local(_) => &[],
            FinalPinTarget::Projection { path, .. } => path,
        }
    }

    /// Whether this target passes through at least one enum variant, i.e.
    /// whether the emitted pin MUST be tester-guarded.
    #[must_use]
    pub fn requires_variant_guard(&self) -> bool {
        self.steps()
            .iter()
            .any(|step| matches!(step, PinStep::Variant { .. }))
    }
}

/// One projected expiry pin: `^<target> == value`, guarded by the testers of
/// every variant step on the way in.
///
/// `value` is the death value tracked by the producer — the last value written
/// through the borrow before its PROVEN expiry. A pin whose death point is not
/// proven must never be constructed; see `projected_expiry`'s emit/disarm table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedFinalPin {
    /// Address of the prophecy carrier.
    pub target: FinalPinTarget,
    /// The value the prophecy is pinned to at the death point.
    pub value: PureExpr,
    /// Human-readable provenance for debug dumps and audit (`"<fn>@bb3/stmt2"`).
    pub provenance: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projection_target_reports_root_and_guard_requirement() {
        let plain = FinalPinTarget::Projection {
            root: "res".into(),
            root_sort: None,
            path: vec![PinStep::Field(0)],
        };
        assert_eq!(plain.root_name(), "res");
        assert!(
            !plain.requires_variant_guard(),
            "a pure tuple projection needs no variant tester"
        );

        let variant = FinalPinTarget::Projection {
            root: "res".into(),
            root_sort: None,
            path: vec![
                PinStep::Variant {
                    ctor: "Some".into(),
                    field: 0,
                },
                PinStep::Field(0),
            ],
        };
        assert!(
            variant.requires_variant_guard(),
            "an enum payload pin MUST be tester-guarded — an unguarded pin on \
             the other variant is a fact about a term that denotes nothing"
        );
        assert_eq!(variant.steps().len(), 2);
    }

    #[test]
    fn local_target_has_no_steps() {
        let local = FinalPinTarget::Local("x".into());
        assert_eq!(local.root_name(), "x");
        assert_eq!(local.steps(), []);
        assert!(!local.requires_variant_guard());
    }
}
