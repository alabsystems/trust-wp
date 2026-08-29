// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod statement;
mod terminator;

pub(super) use statement::process_statements;
pub(super) use terminator::process_terminator;
