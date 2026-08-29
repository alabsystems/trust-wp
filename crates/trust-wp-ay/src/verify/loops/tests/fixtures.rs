// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::verify::loops::LoopVcBase;

pub(super) fn effects<'a>(
    direct: &'a HashMap<String, PureExpr>,
    deref: &'a HashMap<String, PureExpr>,
    double_deref: &'a HashMap<String, PureExpr>,
) -> BodyEffects<'a> {
    BodyEffects::new(direct, deref, double_deref)
}

/// Positional-parameter wrapper for `verify_initialization` (#2657 test compat).
pub(super) fn verify_initialization(
    requires: &[PureExpr],
    invariants: &[PureExpr],
    pre_loop_assignments: &HashMap<String, NamedBindingValue>,
    init_extra_facts: &[PureExpr],
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationResult, crate::error::EncodingError> {
    let empty_direct = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let base = LoopVcBase {
        invariants,
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        effects: BodyEffects::new(&empty_direct, &empty_deref, &empty_double_deref),
        config,
    };
    super::super::initialization::verify_initialization(
        &base,
        requires,
        pre_loop_assignments,
        init_extra_facts,
    )
}

pub(super) fn verify_initialization_outcome(
    requires: &[PureExpr],
    invariants: &[PureExpr],
    pre_loop_assignments: &HashMap<String, NamedBindingValue>,
    init_extra_facts: &[PureExpr],
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationOutcome, crate::error::EncodingError> {
    let empty_direct = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let base = LoopVcBase {
        invariants,
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        effects: BodyEffects::new(&empty_direct, &empty_deref, &empty_double_deref),
        config,
    };
    super::super::initialization::verify_initialization_outcome(
        &base,
        requires,
        pre_loop_assignments,
        init_extra_facts,
    )
}

pub(super) fn postcondition_inputs<'a>(
    ensures: &'a [PureExpr],
    return_expr: Option<&'a PureExpr>,
    pre_loop_assignments: &'a HashMap<String, NamedBindingValue>,
    requires: &'a [PureExpr],
    post_extra_facts: &'a [PureExpr],
) -> PostconditionInputs<'a> {
    PostconditionInputs {
        ensures,
        return_expr,
        pre_loop_assignments,
        requires,
        post_extra_facts,
    }
}

/// Positional-parameter wrapper for `verify_postcondition` (#2657 test compat).
pub(super) fn verify_postcondition(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
    modified_vars: &[&str],
    inputs: PostconditionInputs<'_>,
    body_effects: BodyEffects<'_>,
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationResult, crate::error::EncodingError> {
    let base = LoopVcBase {
        invariants,
        loop_condition,
        condition_is_body_break,
        modified_vars,
        effects: body_effects,
        config,
    };
    super::super::postcondition::verify_postcondition(&base, inputs)
}

pub(super) fn verify_postcondition_outcome(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
    modified_vars: &[&str],
    inputs: PostconditionInputs<'_>,
    body_effects: BodyEffects<'_>,
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationOutcome, crate::error::EncodingError> {
    let base = LoopVcBase {
        invariants,
        loop_condition,
        condition_is_body_break,
        modified_vars,
        effects: body_effects,
        config,
    };
    super::super::postcondition::verify_postcondition_outcome(&base, inputs)
}

/// Positional-parameter wrapper for `verify_variant_nonneg` (#2657 test compat).
pub(super) fn verify_variant_nonneg(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
    variant: &PureExpr,
    modified_vars: &[&str],
    body_effects: BodyEffects<'_>,
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationResult, crate::error::EncodingError> {
    let base = LoopVcBase {
        invariants,
        loop_condition,
        condition_is_body_break,
        modified_vars,
        effects: body_effects,
        config,
    };
    super::super::variant::verify_variant_nonneg(&base, variant)
}

/// Positional-parameter wrapper for `verify_variant_decrease` (#2657 test compat).
pub(super) fn verify_variant_decrease(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
    variant: &PureExpr,
    modified_vars: &[&str],
    body_effects: BodyEffects<'_>,
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationResult, crate::error::EncodingError> {
    let base = LoopVcBase {
        invariants,
        loop_condition,
        condition_is_body_break,
        modified_vars,
        effects: body_effects,
        config,
    };
    super::super::variant::verify_variant_decrease(&base, variant)
}

/// Positional-parameter wrapper for `verify_preservation_with_config` (#2657 test compat).
pub(super) fn verify_preservation_with_config(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
    modified_vars: &[&str],
    body_effects: BodyEffects<'_>,
    config: &LoopEncoderConfig<'_>,
) -> Result<crate::verify::VerificationResult, crate::error::EncodingError> {
    let base = LoopVcBase {
        invariants,
        loop_condition,
        condition_is_body_break,
        modified_vars,
        effects: body_effects,
        config,
    };
    super::super::preservation::verify_preservation_with_config(&base)
}
