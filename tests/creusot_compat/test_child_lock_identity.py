# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Fixture locks preserve package and edge identities across source collisions."""

import pytest

from tests.creusot_compat.harness_project import (
    _parse_lock_packages,
    _resolve_lock_dep,
    _verify_child_lock_subgraph,
)


GIT_SOURCE = "git+https://example.invalid/clean.git?rev=1234"
GIT_LOCK_SOURCE = GIT_SOURCE + "#1234"
ROOT_DEPENDENCIES = ("creusot-contracts", "creusot-std", "trust-wp", "trust-wp-std")


def package(name, dependencies=(), source=None):
    entry = f'[[package]]\nname = "{name}"\nversion = "1.0.0"\n'
    if source is not None:
        entry += f'source = "{source}"\n'
    return entry + "dependencies = [\n" + "".join(
        f' "{dependency}",\n' for dependency in dependencies
    ) + "]\n\n"


def graph(kernel_dependency):
    return "".join(
        package(name, (kernel_dependency,) if name == "trust-wp" else ())
        for name in ROOT_DEPENDENCIES
    ) + package("clean-kernel") + package("clean-kernel", source=GIT_LOCK_SOURCE)


@pytest.mark.parametrize("dependency", [
    "clean-kernel 1.0.0",
    f"clean-kernel 1.0.0 ({GIT_SOURCE})",
])
def test_equal_version_path_and_git_packages_preserve_valid_graph(dependency):
    workspace = graph(dependency)
    _verify_child_lock_subgraph(
        workspace + package("creusot_test", ROOT_DEPENDENCIES), workspace
    )


def test_retargeting_edge_to_equal_version_other_source_is_refused():
    workspace = graph(f"clean-kernel 1.0.0 ({GIT_SOURCE})")
    child = graph("clean-kernel 1.0.0") + package("creusot_test", ROOT_DEPENDENCIES)
    with pytest.raises(RuntimeError, match="edges.*absent"):
        _verify_child_lock_subgraph(child, workspace)


def test_package_from_unreviewed_source_is_refused():
    workspace = graph("clean-kernel 1.0.0")
    child = workspace.replace(GIT_LOCK_SOURCE, GIT_LOCK_SOURCE + "unreviewed")
    with pytest.raises(RuntimeError, match="not in the reviewed workspace lock"):
        _verify_child_lock_subgraph(
            child + package("creusot_test", ROOT_DEPENDENCIES), workspace
        )


def test_ambiguous_unqualified_dependency_is_refused():
    packages = _parse_lock_packages(
        package("kernel", source=GIT_LOCK_SOURCE)
        + package("kernel", source="registry+https://example.invalid/index")
    )
    for dep in ("kernel", "kernel 1.0.0"):
        with pytest.raises(RuntimeError, match="ambiguous or missing"):
            _resolve_lock_dep(dep, {"kernel": packages})


def test_qualified_dependency_requires_matching_source():
    packages = _parse_lock_packages(package("kernel", source=GIT_LOCK_SOURCE))
    with pytest.raises(RuntimeError, match="ambiguous or missing"):
        _resolve_lock_dep(
            "kernel 1.0.0 (registry+https://example.invalid/index)",
            {"kernel": packages},
        )


def test_root_cannot_name_missing_package():
    workspace = graph("clean-kernel 1.0.0")
    child = package("creusot_test", ROOT_DEPENDENCIES)
    with pytest.raises(RuntimeError, match="ambiguous or missing"):
        _verify_child_lock_subgraph(child, workspace)
