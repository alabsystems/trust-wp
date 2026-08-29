// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

pub(super) use super::{helpers::is_into_iter_receiver, rewrite_expr};

fn datatype_var(name: &str, sort_name: &str) -> PureExpr {
    let id = intern_sort_name(sort_name);
    PureExpr::Var(name.to_string(), Some(ExprSort::Datatype(id)))
}

fn into_iter_var(name: &str) -> PureExpr {
    datatype_var(name, "alloc::vec::into_iter::IntoIter")
}

fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

fn option_into_iter_var(name: &str) -> PureExpr {
    let id = intern_sort_name("core::option::IntoIter");
    PureExpr::Var(name.to_string(), Some(ExprSort::Datatype(id)))
}

fn int_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Int))
}

fn range_var(name: &str) -> PureExpr {
    datatype_var(name, "core::ops::range::Range")
}

fn empty_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::sources::empty::Empty")
}

fn once_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::sources::once::Once")
}

fn repeat_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::sources::repeat::Repeat")
}

fn fuse_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::fuse::Fuse")
}

fn cloned_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::cloned::Cloned")
}

fn copied_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::copied::Copied")
}

fn rev_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::rev::Rev")
}

fn skip_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::skip::Skip")
}

fn take_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::take::Take")
}

fn enumerate_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::enumerate::Enumerate")
}

fn zip_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::zip::Zip")
}

fn chain_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::chain::Chain")
}

fn peekable_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::peekable::Peekable")
}

fn map_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::map::Map")
}

fn filter_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::filter::Filter")
}

fn filter_map_var(name: &str) -> PureExpr {
    datatype_var(name, "core::iter::adapters::filter_map::FilterMap")
}

fn map_inv_var(name: &str) -> PureExpr {
    datatype_var(name, "trust_wp_std::std::iter::map_inv::MapInv")
}

fn hash_map_into_iter_var(name: &str) -> PureExpr {
    datatype_var(name, "std::collections::hash_map::IntoIter")
}

fn hash_map_iter_var(name: &str) -> PureExpr {
    datatype_var(name, "std::collections::hash_map::Iter")
}

fn hash_map_iter_mut_var(name: &str) -> PureExpr {
    datatype_var(name, "std::collections::hash_map::IterMut")
}

fn hash_set_into_iter_var(name: &str) -> PureExpr {
    datatype_var(name, "std::collections::hash_set::IntoIter")
}

fn hash_set_iter_var(name: &str) -> PureExpr {
    datatype_var(name, "std::collections::hash_set::Iter")
}

fn slice_iter_var(name: &str) -> PureExpr {
    datatype_var(name, "core::slice::iter::Iter")
}

fn slice_iter_mut_var(name: &str) -> PureExpr {
    datatype_var(name, "core::slice::iter::IterMut")
}

fn wrapped_receiver(expr: PureExpr) -> PureExpr {
    PureExpr::Final(Arc::new(PureExpr::View(Arc::new(PureExpr::Old(Arc::new(
        expr,
    ))))))
}

fn make_produces(recv: PureExpr, visited: PureExpr, next: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "produces".to_string(),
        args: vec![visited, next],
    }
}

fn make_completed(recv: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "completed".to_string(),
        args: vec![],
    }
}

fn make_produces_back(recv: PureExpr, visited: PureExpr, next: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(recv),
        method: "produces_back".to_string(),
        args: vec![visited, next],
    }
}

fn collect_and_clauses<'a>(expr: &'a PureExpr, clauses: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_and_clauses(lhs, clauses);
            collect_and_clauses(rhs, clauses);
        }
        _ => clauses.push(expr),
    }
}

fn flattened_and_clauses(expr: &PureExpr) -> Vec<&PureExpr> {
    let mut clauses = Vec::new();
    collect_and_clauses(expr, &mut clauses);
    clauses
}

mod composite;
mod hash_map;
mod hash_set;
mod helpers;
mod into_iter;
mod range;
mod simple;
