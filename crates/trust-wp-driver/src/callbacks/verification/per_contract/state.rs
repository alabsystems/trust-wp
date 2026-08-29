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
