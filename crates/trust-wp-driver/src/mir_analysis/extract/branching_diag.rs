// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use rustc_middle::mir::{BasicBlock, Body, Location};

use super::{super::diagnostics::ExtractionDiagKind, BlockExtractionContext};

pub(super) fn record_switch_diag(
    ctx: &BlockExtractionContext<'_>,
    body: &Body<'_>,
    bb: BasicBlock,
    kind: ExtractionDiagKind,
    detail: impl Into<String>,
) {
    ctx.record_diag(
        "extract/branching.rs",
        kind,
        detail,
        Some(Location {
            block: bb,
            statement_index: body.basic_blocks[bb].statements.len(),
        }),
    );
}
