// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop solver configuration helpers.

use trust_wp_ay::LoopEncoderConfig;

use super::types::LoopWithInvariantRequest;

/// Extracts the solver-configuration fields that every loop verification
/// call forwards unchanged. Centralizes the mapping so adding a new config
/// field requires updating only this function.
pub(super) fn encoder_config_from_req<'a>(
    req: &LoopWithInvariantRequest<'a>,
) -> LoopEncoderConfig<'a> {
    let mut config = LoopEncoderConfig::default();
    if let Some(invs) = req.type_invariants {
        config = config.with_type_invariants(invs);
    }
    if let Some(fns) = req.logic_fns {
        config = config.with_logic_fns(fns);
    }
    if let Some(modes) = req.mode_overrides {
        config = config.with_mode_overrides(modes);
    }
    if let Some(constants) = req.type_constants {
        config = config.with_type_constants(constants);
    }
    if let Some(track) = req.track {
        config = config.with_track(track);
    }
    if let Some(timeout) = req.timeout {
        config = config.with_timeout(timeout);
    }
    if let Some(decls) = req.adt_decls {
        config = config.with_adt_decls(decls);
    }
    if let Some(ranges) = req.adt_field_ranges {
        config = config.with_adt_field_ranges(ranges);
    }
    config
}
