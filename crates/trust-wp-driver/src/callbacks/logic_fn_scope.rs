// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function visibility scoping and name normalization.
//!
//! Contains `scope_logic_fn_modes`, `build_logic_fn_path_map`,
//! `normalize_logic_fn_names`, and `parent_module`.

use std::collections::{HashMap, HashSet};

use trust_wp_core::{
    formula::{CaptureAvoidingSubstOptions, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

/// Extract the parent module from a fully qualified Rust path.
///
/// For `crate::specs::max`, returns `"crate::specs"`.
/// For `max` (no module), returns `""`.
pub(super) fn parent_module(full_path: &str) -> &str {
    full_path.rsplit_once("::").map_or("", |(parent, _)| parent)
}

/// Check whether a caller and a logic function share the same scope after
/// normalizing trait impl paths.
///
/// Trait impl paths like `crate::<T as Trait>::method` have parent
/// `crate::<T as Trait>`, while the corresponding trait definition
/// `crate::Trait::f` has parent `crate::Trait`. These don't match
/// via `parent_module`, but both conceptually reside in `crate`.
///
/// This function only activates when at least one path contains `<`
/// (trait impl syntax). It extracts the module prefix before the `<`
/// on the impl side, and checks that the other side's parent module
/// starts with (or equals) that prefix. (#2676)
fn same_trait_scope(caller_path: &str, fn_path: &str) -> bool {
    let caller_has_impl = caller_path.contains('<');
    let fn_has_impl = fn_path.contains('<');
    if !caller_has_impl && !fn_has_impl {
        return false;
    }
    let caller_base = if caller_has_impl {
        trait_impl_prefix(caller_path)
    } else {
        parent_module(caller_path)
    };
    let fn_base = if fn_has_impl {
        trait_impl_prefix(fn_path)
    } else {
        parent_module(fn_path)
    };
    // One prefix is the impl's module (e.g., "crate"), the other is the trait's
    // namespace (e.g., "crate::Trait"). The trait is defined in the impl's module
    // if the impl prefix is a `::` ancestor of the trait's parent.
    is_module_ancestor_or_equal(caller_base, fn_base)
        || is_module_ancestor_or_equal(fn_base, caller_base)
}

/// For a trait impl path `crate::<T as Trait>::method`, extract `"crate"`.
fn trait_impl_prefix(full_path: &str) -> &str {
    if let Some(angle_pos) = full_path.find('<') {
        let prefix = &full_path[..angle_pos];
        prefix.strip_suffix("::").unwrap_or(prefix)
    } else {
        parent_module(full_path)
    }
}

/// Check if `ancestor` is equal to or a `::` prefix of `descendant`.
fn is_module_ancestor_or_equal(ancestor: &str, descendant: &str) -> bool {
    if ancestor == descendant {
        return true;
    }
    descendant.starts_with(ancestor) && descendant.as_bytes().get(ancestor.len()) == Some(&b':')
}

fn crate_relative_logic_fn_path(full_path: &str) -> Option<&str> {
    let (_, relative) = full_path.split_once("::")?;
    (!relative.is_empty()).then_some(relative)
}

/// Register both crate-qualified and crate-relative aliases for a logic function path.
pub(super) fn insert_logic_fn_path_aliases(set: &mut HashSet<String>, full_path: &str) {
    set.insert(full_path.to_string());
    if let Some(relative) = crate_relative_logic_fn_path(full_path) {
        set.insert(relative.to_string());
    }
}

/// Scope logic function visibility based on the caller's location (#519, #540).
///
/// - `Default` (bare `#[logic]`): module-level scoping — body visible only
///   within the same module, opaque elsewhere.
/// - `OpenSelf` (`#[logic(open(self))]`): module-level scoping — body visible
///   only within the same module, opaque elsewhere.
/// - `Open` and `Prophetic`: pass through unchanged — visible everywhere.
///
/// The encoder suppresses axioms for `Default` mode, so the downgrade
/// effectively makes the function opaque to out-of-scope callers.
pub(super) fn scope_logic_fn_modes(
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
    caller_def_path: &str,
) -> Vec<LogicMode> {
    let caller_module = parent_module(caller_def_path);
    logic_fns
        .iter()
        .map(|lf| match lf.mode() {
            LogicMode::Default | LogicMode::OpenSelf => {
                let fn_module = parent_module(lf.full_path());
                // Direct module match (common case: plain functions in same module).
                if fn_module == caller_module {
                    return LogicMode::Open;
                }
                // Trait impl normalization: when a trait impl method calls a trait-
                // defined logic function, `parent_module` yields mismatched paths
                // (e.g., `crate::<T as Foo>` vs `crate::Foo`). Fall back to
                // prefix-based scope matching that strips the `<...>` impl block
                // and checks the trait is defined in the same module. (#2676)
                if same_trait_scope(caller_def_path, lf.full_path()) {
                    LogicMode::Open
                } else {
                    LogicMode::Default
                }
            }
            _ => lf.mode(),
        })
        .collect()
}

/// Build a mapping from module-qualified logic function paths to their
/// registered short names.
///
/// The contract parser preserves module paths in `LogicFnCall` names
/// (e.g., `x::transparent` from `proof_assert!(x::transparent())`), but
/// logic functions are registered with their short name (e.g., `transparent`).
/// This mapping enables normalization so the SMT encoder finds the
/// registered function declaration instead of creating a free placeholder.
///
/// Re: #746
pub(super) fn build_logic_fn_path_map(
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> HashMap<String, String> {
    let mut map = HashMap::new();
    for lf in logic_fns {
        // Map full_path -> name (e.g., "creusot_test::x::transparent" -> "transparent")
        if lf.full_path() != lf.name() && lf.full_path().contains("::") {
            map.insert(lf.full_path().to_string(), lf.name().to_string());
            // A short-name collision member is identified by its unique id. A
            // crate-relative spelling (`x::k`) is only that path at the crate
            // root; elsewhere it is resolved in the owner's scope
            // (`logic::identity`), never here.
            if lf.has_unique_id() {
                continue;
            }

            // Also map the module-relative path (without crate prefix) to the
            // short name. The contract parser preserves source-level paths like
            // `x::transparent` from `proof_assert!(x::transparent())`, which lack
            // the crate prefix that full_path() includes. Without this mapping,
            // module-qualified logic function calls in proof_asserts are not
            // normalized and fall through as unresolved placeholders. (#1370)
            if let Some(relative) = crate_relative_logic_fn_path(lf.full_path()) {
                if relative != lf.name() {
                    map.insert(relative.to_string(), lf.name().to_string());
                }
            }
        }
    }
    map
}

/// Build aliases for associated logic functions referenced through `Self::`.
///
/// Contract clauses on trait impl methods may preserve calls like
/// `Self::hash_log(..)` after parsing. Logic functions are registered by their
/// short names, so an otherwise in-scope impl-local associated logic function
/// needs a local alias from `Self::<name>` to `<name>`.
///
/// Keep this stricter than `same_trait_scope`: a trait declaration such as
/// `crate::Hash::hash_log` is visible to an impl method for opacity purposes,
/// but the concrete `Self::hash_log` call inside `crate::<usize as Hash>::hash`
/// should resolve only to an associated logic function defined in that same
/// impl/type parent.
pub(super) fn build_scoped_self_logic_fn_path_map(
    logic_fns: &[LogicFnDef],
    caller_def_path: &str,
) -> HashMap<String, String> {
    let caller_module = parent_module(caller_def_path);
    let mut map = HashMap::new();
    for lf in logic_fns {
        if parent_module(lf.full_path()) == caller_module {
            // Same impl/type parent as the caller: `Self::<short>` is exactly
            // this definition (its unique id when the short name collides).
            map.insert(format!("Self::{}", lf.short_name()), lf.name().to_string());
        }
    }
    map
}

fn build_scoped_self_logic_fn_inline_map<'a>(
    logic_fns: &'a [LogicFnDef],
    caller_def_path: &str,
) -> HashMap<String, &'a LogicFnDef> {
    let caller_module = parent_module(caller_def_path);
    let mut map = HashMap::new();
    for lf in logic_fns {
        if parent_module(lf.full_path()) == caller_module
            && lf.requires().is_empty()
            && !lf.is_recursive()
        {
            map.insert(format!("Self::{}", lf.short_name()), lf);
            // Already resolved to this ASSOCIATED definition in the owner's
            // scope (`Self::m`). Every local definition carries a unique id,
            // so a free function's id must not make this `Self::`-only
            // inliner expand ordinary free logic calls.
            let associated = lf.has_unique_id()
                && trust_wp_core::logic::identity::logic_fn_identity_registry().is_some_and(
                    |registry| {
                        registry.member(lf.name()).is_some_and(|member| {
                            member.kind != trust_wp_core::logic::identity::LogicFnOwnerKind::Free
                        })
                    },
                );
            if associated {
                map.insert(lf.name().to_string(), lf);
            }
        }
    }
    map
}

/// Inline same-parent `Self::` logic-function calls that are safe to expand
/// locally.
///
/// This is intentionally narrower than normal logic-function unfolding:
/// only associated calls spelled `Self::foo` and defined in the caller's exact
/// impl/type parent are considered, and calls with preconditions or recursive
/// bodies are left as logic-function calls.
pub(super) fn inline_scoped_self_logic_fn_calls(
    expr: PureExpr,
    logic_fns: &[LogicFnDef],
    caller_def_path: &str,
) -> PureExpr {
    let inline_map = build_scoped_self_logic_fn_inline_map(logic_fns, caller_def_path);
    if inline_map.is_empty() {
        return expr;
    }

    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } => {
            let Some(logic_fn) = inline_map.get(&name) else {
                return PureExpr::LogicFnCall { name, args };
            };
            if logic_fn.params().len() != args.len() {
                return PureExpr::LogicFnCall { name, args };
            }
            let substitutions: HashMap<String, PureExpr> =
                logic_fn.params().iter().cloned().zip(args).collect();
            logic_fn.body().substitute_capture_avoiding(
                &substitutions,
                &CaptureAvoidingSubstOptions::default(),
            )
        }
        other => other,
    })
}

/// Normalize logic function call names in an expression tree.
///
/// Replaces module-qualified names (e.g., `x::transparent`) with short names
/// (e.g., `transparent`) using the mapping from `build_logic_fn_path_map`.
/// This ensures `LogicFnCall` names match the registered logic function
/// declarations in the SMT encoder.
///
/// Re: #746
pub(super) fn normalize_logic_fn_names(
    expr: PureExpr,
    path_map: &HashMap<String, String>,
) -> PureExpr {
    if path_map.is_empty() {
        return expr;
    }
    normalize_logic_fn_names_inner(expr, path_map)
}

#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
fn normalize_logic_fn_names_inner(expr: PureExpr, path_map: &HashMap<String, String>) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: path_map.get(&name).cloned().unwrap_or(name),
            args,
        },
        other => other,
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use trust_wp_core::{
        formula::{BinOp, ExprSort, MatchArm, Pattern, PureExpr},
        logic::LogicFnDef,
    };

    use super::{
        build_scoped_self_logic_fn_path_map, inline_scoped_self_logic_fn_calls,
        insert_logic_fn_path_aliases, is_module_ancestor_or_equal, normalize_logic_fn_names,
        same_trait_scope, trait_impl_prefix,
    };

    #[test]
    fn test_logic_fn_path_aliases_insert_full_and_crate_relative_paths() {
        let mut paths = std::collections::HashSet::new();

        insert_logic_fn_path_aliases(&mut paths, "crate_name::specs::helper");

        assert!(paths.contains("crate_name::specs::helper"));
        assert!(paths.contains("specs::helper"));
    }

    #[test]
    fn test_logic_fn_path_aliases_do_not_insert_leaf_name() {
        let mut paths = std::collections::HashSet::new();

        insert_logic_fn_path_aliases(&mut paths, "crate_name::specs::helper");

        assert!(!paths.contains("helper"));
    }

    #[test]
    fn test_normalize_logic_fn_names_rewrites_closure_match_bodies() {
        let expr = PureExpr::Closure {
            params: vec![("self".to_string(), Some(ExprSort::Int))],
            body: Arc::new(PureExpr::Match {
                scrutinee: Arc::new(PureExpr::Var("tag".to_string(), None)),
                arms: vec![MatchArm {
                    pattern: Pattern::Binding("bound".to_string()),
                    body: PureExpr::LogicFnCall {
                        name: "crate_name::specs::helper".to_string(),
                        args: vec![],
                    },
                }],
            }),
        };
        let path_map = HashMap::from([(
            "crate_name::specs::helper".to_string(),
            "helper".to_string(),
        )]);

        let normalized = normalize_logic_fn_names(expr, &path_map);

        assert_eq!(
            normalized,
            PureExpr::Closure {
                params: vec![("self".to_string(), Some(ExprSort::Int))],
                body: Arc::new(PureExpr::Match {
                    scrutinee: Arc::new(PureExpr::Var("tag".to_string(), None)),
                    arms: vec![MatchArm {
                        pattern: Pattern::Binding("bound".to_string()),
                        body: PureExpr::LogicFnCall {
                            name: "helper".to_string(),
                            args: vec![],
                        },
                    }],
                }),
            }
        );
    }

    #[test]
    fn test_scoped_self_logic_fn_map_uses_same_impl_parent() {
        let trait_decl = LogicFnDef::new(
            "hash_log".to_string(),
            "creusot_test::Hash::hash_log".to_string(),
            vec!["x".to_string()],
            PureExpr::Int(0),
        );
        let impl_def = LogicFnDef::new(
            "hash_log".to_string(),
            "creusot_test::<usize as Hash>::hash_log".to_string(),
            vec!["x".to_string()],
            PureExpr::Var("x".to_string(), None),
        );

        let map = build_scoped_self_logic_fn_path_map(
            &[trait_decl, impl_def],
            "creusot_test::<usize as Hash>::hash",
        );

        assert_eq!(
            map.get("Self::hash_log").map(String::as_str),
            Some("hash_log")
        );
        assert!(!map.contains_key("K::hash_log"));
    }

    #[test]
    fn test_scoped_self_logic_fn_map_skips_trait_parent_for_impl_caller() {
        let trait_decl = LogicFnDef::new(
            "hash_log".to_string(),
            "creusot_test::Hash::hash_log".to_string(),
            vec!["x".to_string()],
            PureExpr::Int(0),
        );

        let map = build_scoped_self_logic_fn_path_map(
            &[trait_decl],
            "creusot_test::<usize as Hash>::hash",
        );

        assert!(!map.contains_key("Self::hash_log"));
    }

    #[test]
    fn test_scoped_self_logic_fn_normalization_leaves_type_param_calls() {
        let map = HashMap::from([("Self::hash_log".to_string(), "hash_log".to_string())]);
        let expr = PureExpr::LogicFnCall {
            name: "Self::hash_log".to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "K::hash_log".to_string(),
                args: vec![PureExpr::Var("k".to_string(), None)],
            }],
        };

        let normalized = normalize_logic_fn_names(expr, &map);

        assert_eq!(
            normalized,
            PureExpr::LogicFnCall {
                name: "hash_log".to_string(),
                args: vec![PureExpr::LogicFnCall {
                    name: "K::hash_log".to_string(),
                    args: vec![PureExpr::Var("k".to_string(), None)],
                }],
            }
        );
    }

    #[test]
    fn test_inline_scoped_self_logic_fn_call_uses_impl_body() {
        let trait_decl = LogicFnDef::new(
            "hash_log".to_string(),
            "creusot_test::Hash::hash_log".to_string(),
            vec!["x".to_string()],
            PureExpr::Int(0),
        );
        let impl_def = LogicFnDef::new(
            "hash_log".to_string(),
            "creusot_test::<usize as Hash>::hash_log".to_string(),
            vec!["x".to_string()],
            PureExpr::Var("x".to_string(), None),
        );
        let arg = PureExpr::LogicFnCall {
            name: "K::hash_log".to_string(),
            args: vec![PureExpr::Var("k".to_string(), None)],
        };
        let expr = PureExpr::LogicFnCall {
            name: "Self::hash_log".to_string(),
            args: vec![arg.clone()],
        };

        let inlined = inline_scoped_self_logic_fn_calls(
            expr,
            &[trait_decl, impl_def],
            "creusot_test::<usize as Hash>::hash",
        );

        assert_eq!(inlined, arg);
    }

    #[test]
    fn test_inline_scoped_self_logic_fn_call_skips_preconditioned_body() {
        let logic_fn = LogicFnDef::new_with_requires(
            "checked".to_string(),
            "creusot_test::<usize as Hash>::checked".to_string(),
            vec!["x".to_string()],
            vec![PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )],
            PureExpr::Var("x".to_string(), None),
        );
        let expr = PureExpr::LogicFnCall {
            name: "Self::checked".to_string(),
            args: vec![PureExpr::Var("k".to_string(), None)],
        };

        let inlined = inline_scoped_self_logic_fn_calls(
            expr.clone(),
            &[logic_fn],
            "creusot_test::<usize as Hash>::hash",
        );

        assert_eq!(inlined, expr);
    }

    // --- trait impl prefix extraction ---

    #[test]
    fn test_trait_impl_prefix_strips_angle_bracket_block() {
        assert_eq!(trait_impl_prefix("crate::<() as Foo>::g"), "crate");
    }

    #[test]
    fn test_trait_impl_prefix_nested_module() {
        assert_eq!(
            trait_impl_prefix("crate::inner::<Struct as Trait>::method"),
            "crate::inner"
        );
    }

    #[test]
    fn test_trait_impl_prefix_no_angles_falls_back_to_parent_module() {
        assert_eq!(trait_impl_prefix("crate::Foo::f"), "crate::Foo");
    }

    // --- module ancestor check ---

    #[test]
    fn test_is_module_ancestor_or_equal_same() {
        assert!(is_module_ancestor_or_equal("crate", "crate"));
    }

    #[test]
    fn test_is_module_ancestor_or_equal_ancestor() {
        assert!(is_module_ancestor_or_equal("crate", "crate::Foo"));
    }

    #[test]
    fn test_is_module_ancestor_or_equal_not_prefix() {
        assert!(!is_module_ancestor_or_equal("crate::a", "crate::b"));
    }

    #[test]
    fn test_is_module_ancestor_or_equal_partial_prefix_not_boundary() {
        // "crate::Fo" is a prefix of "crate::Foo" but not at a `::` boundary.
        assert!(!is_module_ancestor_or_equal("crate::Fo", "crate::Foo"));
    }

    // --- same_trait_scope integration ---

    #[test]
    fn test_same_trait_scope_impl_calls_trait_logic_fn() {
        // call_in_contract.rs pattern: impl method calling trait-defined logic fn
        assert!(same_trait_scope(
            "creusot_test::<() as Foo>::g",
            "creusot_test::Foo::f",
        ));
    }

    #[test]
    fn test_same_trait_scope_nested_module_impl() {
        assert!(same_trait_scope(
            "crate::inner::<Struct as Trait>::method",
            "crate::inner::Trait::logic_fn",
        ));
    }

    #[test]
    fn test_same_trait_scope_different_modules_rejected() {
        // Trait in a different module should not match.
        assert!(!same_trait_scope(
            "crate::mod_a::<Struct as Trait>::method",
            "crate::mod_b::Trait::logic_fn",
        ));
    }

    #[test]
    fn test_same_trait_scope_no_impl_syntax_returns_false() {
        // Two plain module paths — same_trait_scope should not activate.
        assert!(!same_trait_scope(
            "crate::mod1::func",
            "crate::mod1::other_func",
        ));
    }

    #[test]
    fn test_same_trait_scope_different_crate_rejected() {
        assert!(!same_trait_scope(
            "crate_a::<T as Foo>::method",
            "crate_b::Foo::logic_fn",
        ));
    }
}
