// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use rustc_middle::ty::TyCtxt;
use trust_wp_core::logic::LogicFnDef;

use super::super::{
    super::{
        proof_assert_verify::ProofAssertSetup,
        verification_context::{ProofAssertContext, VerificationRunConfig},
    },
    PreparedVerification,
};

pub(in crate::callbacks::verification) struct SharedVerificationState<'a, 'tcx> {
    pub(in crate::callbacks::verification) tcx: TyCtxt<'tcx>,
    pub(in crate::callbacks::verification) config: VerificationRunConfig<'a>,
    pub(in crate::callbacks::verification) prep: &'a PreparedVerification<'a>,
    pub(in crate::callbacks::verification) logic_fns: &'a [LogicFnDef],
    pub(in crate::callbacks::verification) pa_setup: &'a ProofAssertSetup<'a>,
    pub(in crate::callbacks::verification) pa_ctx: ProofAssertContext<'a>,
    pub(in crate::callbacks::verification) pa_logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(in crate::callbacks::verification) unverified_axioms: &'a HashSet<String>,
}

/// Which lane owns a function's contract verdict.
///
/// A lane that owns the verdict (the loop lane, the recursive-`#[variant]`
/// lane) must not `return` from inside `verify_single_contract`: such a return
/// silently skips everything after it — most importantly the in-function
/// `proof_assert!` pass, which is not part of the contract verdict at all and
/// must run whichever lane was taken. Skipping it is an exit-0 false accept
/// (D-38; `s53_pa_false_after_loop_lane.rs`, `s61_variant_lane_pa_false.rs`).
/// The lanes record their choice here and fall through to one shared tail.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum FunctionLanePlan {
    /// No lane claimed the verdict: build and discharge the function-level VC.
    FunctionVc,
    /// A lane (loop or recursive variant) already reported this function's
    /// contract verdict; the function-level VC must not report a second one.
    LaneOwnsVerdict,
}

impl FunctionLanePlan {
    pub(super) fn runs_function_vc(self) -> bool {
        matches!(self, Self::FunctionVc)
    }
}
