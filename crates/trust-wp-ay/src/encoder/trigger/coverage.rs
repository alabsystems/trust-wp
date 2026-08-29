// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Coverage tracking infrastructure for trigger synthesis.
//!
//! Provides `QuantifiedVarIndex` and `QuantifiedVarCoverage` for tracking
//! which bound variables a candidate trigger covers. Uses a bitmask
//! representation for up to 128 variables, with a fallback to `HashSet`.

use std::collections::{HashMap, HashSet};

use trust_wp_core::formula::PureExpr;

pub(super) type CoverageMask = u128;

#[derive(Clone, Debug)]
pub(super) enum QuantifiedVarCoverage {
    Mask(CoverageMask),
    Names(HashSet<String>),
}

impl QuantifiedVarCoverage {
    pub(super) fn is_empty(&self) -> bool {
        match self {
            Self::Mask(mask) => *mask == 0,
            Self::Names(names) => names.is_empty(),
        }
    }
}

struct MaskedQuantifiedVarIndex<'a> {
    slots: HashMap<&'a str, u32>,
    full_mask: CoverageMask,
}

pub(super) struct QuantifiedVarIndex<'a> {
    kind: QuantifiedVarIndexKind<'a>,
}

enum QuantifiedVarIndexKind<'a> {
    Masked(MaskedQuantifiedVarIndex<'a>),
    Names(HashSet<&'a str>),
}

#[derive(Clone, Copy)]
pub(super) enum DepthOverflowPolicy {
    EmptyCoverage,
    FullCoverage,
}

impl<'a> QuantifiedVarIndex<'a> {
    pub(super) fn new(vars: &'a [String]) -> Self {
        let mut unique = Vec::new();
        let mut seen = HashSet::new();
        for var in vars {
            if seen.insert(var.as_str()) {
                unique.push(var.as_str());
            }
        }
        if unique.len() <= CoverageMask::BITS as usize {
            let mut slots = HashMap::with_capacity(unique.len());
            let mut full_mask = 0;
            for (slot, name) in unique.into_iter().enumerate() {
                let slot = u32::try_from(slot).expect("slot count fits in u32");
                slots.insert(name, slot);
                full_mask |= 1u128 << slot;
            }
            Self {
                kind: QuantifiedVarIndexKind::Masked(MaskedQuantifiedVarIndex { slots, full_mask }),
            }
        } else {
            Self {
                kind: QuantifiedVarIndexKind::Names(seen),
            }
        }
    }

    pub(super) fn empty_coverage(&self) -> QuantifiedVarCoverage {
        match &self.kind {
            QuantifiedVarIndexKind::Masked(_) => QuantifiedVarCoverage::Mask(0),
            QuantifiedVarIndexKind::Names(_) => QuantifiedVarCoverage::Names(HashSet::new()),
        }
    }

    pub(super) fn full_coverage(&self) -> QuantifiedVarCoverage {
        match &self.kind {
            QuantifiedVarIndexKind::Masked(index) => QuantifiedVarCoverage::Mask(index.full_mask),
            QuantifiedVarIndexKind::Names(names) => {
                QuantifiedVarCoverage::Names(names.iter().map(|name| (*name).to_string()).collect())
            }
        }
    }

    pub(super) fn coverage_for_var(&self, name: &str) -> QuantifiedVarCoverage {
        match &self.kind {
            QuantifiedVarIndexKind::Masked(index) => {
                let mask = index.slots.get(name).map_or(0, |slot| 1u128 << *slot);
                QuantifiedVarCoverage::Mask(mask)
            }
            QuantifiedVarIndexKind::Names(names) => {
                if names.contains(name) {
                    QuantifiedVarCoverage::Names(HashSet::from([name.to_string()]))
                } else {
                    QuantifiedVarCoverage::Names(HashSet::new())
                }
            }
        }
    }

    pub(super) fn merge_coverage(
        coverage: &mut QuantifiedVarCoverage,
        other: QuantifiedVarCoverage,
    ) {
        match (coverage, other) {
            (QuantifiedVarCoverage::Mask(mask), QuantifiedVarCoverage::Mask(other_mask)) => {
                *mask |= other_mask;
            }
            (QuantifiedVarCoverage::Names(names), QuantifiedVarCoverage::Names(other_names)) => {
                names.extend(other_names);
            }
            _ => unreachable!("coverage representation must match quantified-var index mode"),
        }
    }

    pub(super) fn coverage_count(coverage: &QuantifiedVarCoverage) -> usize {
        match coverage {
            QuantifiedVarCoverage::Mask(mask) => mask.count_ones() as usize,
            QuantifiedVarCoverage::Names(names) => names.len(),
        }
    }

    pub(super) fn coverage_contains(&self, coverage: &QuantifiedVarCoverage, name: &str) -> bool {
        match (&self.kind, coverage) {
            (QuantifiedVarIndexKind::Masked(index), QuantifiedVarCoverage::Mask(mask)) => index
                .slots
                .get(name)
                .is_some_and(|slot| (*mask & (1u128 << *slot)) != 0),
            (QuantifiedVarIndexKind::Names(_), QuantifiedVarCoverage::Names(names)) => {
                names.contains(name)
            }
            _ => unreachable!("coverage representation must match quantified-var index mode"),
        }
    }

    pub(super) fn coverage_is_full(&self, coverage: &QuantifiedVarCoverage) -> bool {
        match (&self.kind, coverage) {
            (QuantifiedVarIndexKind::Masked(index), QuantifiedVarCoverage::Mask(mask)) => {
                *mask == index.full_mask
            }
            (QuantifiedVarIndexKind::Names(names), QuantifiedVarCoverage::Names(found)) => {
                found.len() == names.len()
            }
            _ => unreachable!("coverage representation must match quantified-var index mode"),
        }
    }

    pub(super) fn combined_coverage_is_full(
        &self,
        left: &QuantifiedVarCoverage,
        right: &QuantifiedVarCoverage,
    ) -> bool {
        match (&self.kind, left, right) {
            (
                QuantifiedVarIndexKind::Masked(index),
                QuantifiedVarCoverage::Mask(left_mask),
                QuantifiedVarCoverage::Mask(right_mask),
            ) => (*left_mask | *right_mask) == index.full_mask,
            (
                QuantifiedVarIndexKind::Names(names),
                QuantifiedVarCoverage::Names(left_names),
                QuantifiedVarCoverage::Names(right_names),
            ) => {
                let mut combined: HashSet<&str> = left_names.iter().map(String::as_str).collect();
                combined.extend(right_names.iter().map(String::as_str));
                combined.len() == names.len()
            }
            _ => unreachable!("coverage representation must match quantified-var index mode"),
        }
    }

    pub(super) fn new_coverage_count(
        coverage: &QuantifiedVarCoverage,
        uncovered: &QuantifiedVarCoverage,
    ) -> usize {
        match (coverage, uncovered) {
            (QuantifiedVarCoverage::Mask(mask), QuantifiedVarCoverage::Mask(uncovered_mask)) => {
                (*mask & *uncovered_mask).count_ones() as usize
            }
            (
                QuantifiedVarCoverage::Names(names),
                QuantifiedVarCoverage::Names(uncovered_names),
            ) => names
                .iter()
                .filter(|name| uncovered_names.contains(*name))
                .count(),
            _ => unreachable!("coverage representation must match quantified-var index mode"),
        }
    }

    pub(super) fn remove_from_uncovered(
        uncovered: &mut QuantifiedVarCoverage,
        coverage: &QuantifiedVarCoverage,
    ) {
        match (uncovered, coverage) {
            (QuantifiedVarCoverage::Mask(uncovered_mask), QuantifiedVarCoverage::Mask(mask)) => {
                *uncovered_mask &= !*mask;
            }
            (
                QuantifiedVarCoverage::Names(uncovered_names),
                QuantifiedVarCoverage::Names(names),
            ) => {
                for name in names {
                    uncovered_names.remove(name);
                }
            }
            _ => unreachable!("coverage representation must match quantified-var index mode"),
        }
    }
}

pub(crate) struct QuantifiedVarUsage<'a> {
    index: QuantifiedVarIndex<'a>,
    coverage: QuantifiedVarCoverage,
}

impl QuantifiedVarUsage<'_> {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn mentions_any(&self) -> bool {
        !self.coverage.is_empty()
    }

    pub(crate) fn mentions(&self, name: &str) -> bool {
        self.index.coverage_contains(&self.coverage, name)
    }
}

pub(crate) fn collect_quantified_var_usage<'a>(
    vars: &'a [String],
    expr: &PureExpr,
) -> QuantifiedVarUsage<'a> {
    let index = QuantifiedVarIndex::new(vars);
    let coverage = super::walker::collect_quantified_coverage(expr, &index, &mut HashSet::new(), 0);
    QuantifiedVarUsage { index, coverage }
}

/// A trigger candidate: a sub-expression and the bound variables it covers.
pub(crate) struct TriggerCandidate<'a> {
    pub(crate) expr: &'a PureExpr,
    pub(super) coverage: QuantifiedVarCoverage,
    /// Lower is better. Based on specificity and depth.
    pub(super) score: i32,
}

pub(super) trait CandidateSink<'a> {
    fn push(&mut self, expr: &'a PureExpr, coverage: QuantifiedVarCoverage, score: i32);
}

pub(super) struct NoCandidateSink;

impl<'a> CandidateSink<'a> for NoCandidateSink {
    fn push(&mut self, _expr: &'a PureExpr, _coverage: QuantifiedVarCoverage, _score: i32) {}
}

pub(super) struct VecCandidateSink<'expr, 'vec> {
    pub(super) candidates: &'vec mut Vec<TriggerCandidate<'expr>>,
}

impl<'expr> CandidateSink<'expr> for VecCandidateSink<'expr, '_> {
    fn push(&mut self, expr: &'expr PureExpr, coverage: QuantifiedVarCoverage, score: i32) {
        self.candidates.push(TriggerCandidate {
            expr,
            coverage,
            score,
        });
    }
}
