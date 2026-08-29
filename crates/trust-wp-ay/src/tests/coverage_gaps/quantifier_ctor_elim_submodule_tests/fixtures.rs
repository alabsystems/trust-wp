// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── Datatype fixtures ──────────────────────────────────────────────────

pub(crate) fn option_int_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    }
}

pub(crate) fn pair_int_bool_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "PairIntBool".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "pair_fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "pair_snd".to_string(),
                    sort: Sort::Bool,
                },
            ],
        }],
    }
}

pub(crate) fn result_int_int_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    }
}

pub(crate) fn state_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "State".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "On".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Off".to_string(),
                fields: vec![],
            },
        ],
    }
}
