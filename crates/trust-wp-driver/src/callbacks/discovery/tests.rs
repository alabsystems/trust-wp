// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;

use super::{
    find_contract_functions, is_bodyful_trait_method,
    source_parsing::extract_attr_args_from_source,
    trusted::{has_attr_without_args_from_source, has_doc_marker_in_header_source},
};
mod attr_source_extraction;
mod bodyless_trait_guard;
mod trait_default_discovery;
