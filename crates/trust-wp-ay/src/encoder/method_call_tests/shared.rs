// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn sample_point_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "Point".to_string(),
        AdtDecl::new(
            "crate::Point".to_string(),
            "Point".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Point".to_string(),
                "Point".to_string(),
                vec![
                    AdtFieldDecl::new("x".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("y".to_string(), ExprSort::Int),
                ],
            )],
        ),
    )])
}

pub(super) fn sample_bucket_map_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "BucketMap".to_string(),
        AdtDecl::new(
            "crate::BucketMap".to_string(),
            "BucketMap".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "BucketMap".to_string(),
                "BucketMap".to_string(),
                vec![AdtFieldDecl::new("buckets".to_string(), ExprSort::Seq)],
            )],
        ),
    )])
}

pub(super) fn sample_own_result_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )])
}

pub(super) fn drifted_list_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "List".to_string(),
        AdtDecl::new(
            "crate::List".to_string(),
            "List".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "List".to_string(),
                "List".to_string(),
                vec![AdtFieldDecl::new("head".to_string(), ExprSort::Int)],
            )],
        ),
    )])
}
