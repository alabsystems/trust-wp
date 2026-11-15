#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Parity checks for the Trust importer dependency mode."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.10 compatibility
    import tomli as tomllib  # type: ignore[no-redef]


WORKSPACE_ROOT = Path(__file__).resolve().parent.parent
TRUST_IR_PATHS = {
    "trust-ir": "../trust-ir/crates/trust-ir",
    "trust-ir-contract": "../trust-ir/crates/trust-ir-contract",
    "trust-ir-build": "../trust-ir/crates/trust-ir-build",
}


def _workspace_table(path: Path) -> dict[str, object]:
    manifest = tomllib.loads(path.read_text(encoding="utf-8"))
    return manifest["workspace"]


def _with_sibling_ir_sources(workspace: dict[str, object]) -> dict[str, object]:
    standalone = deepcopy(workspace)
    standalone_dependencies = standalone["dependencies"]
    assert isinstance(standalone_dependencies, dict)
    for name, path in TRUST_IR_PATHS.items():
        provider = standalone_dependencies[name]
        assert isinstance(provider, dict)
        for selector in ("git", "rev", "branch", "tag"):
            provider.pop(selector, None)
        provider["path"] = path
    return standalone


def test_trust_dependency_mode_matches_root_except_trust_ir_source() -> None:
    standalone = _with_sibling_ir_sources(_workspace_table(WORKSPACE_ROOT / "Cargo.toml"))
    trust_mode = _workspace_table(
        WORKSPACE_ROOT / "dependency-modes" / "trust" / "Cargo.toml"
    )

    assert trust_mode == standalone


def test_source_replacement_preserves_every_provider_setting() -> None:
    standalone = _workspace_table(WORKSPACE_ROOT / "Cargo.toml")
    trust_mode = _workspace_table(
        WORKSPACE_ROOT / "dependency-modes" / "trust" / "Cargo.toml"
    )
    for name in TRUST_IR_PATHS:
        for setting, value in (
            ("features", ["different-proof-environment"]),
            ("default-features", not standalone["dependencies"][name].get("default-features", True)),
            ("optional", True),
            ("package", "different-native-provider"),
        ):
            changed = deepcopy(standalone)
            changed["dependencies"][name][setting] = value
            converted = _with_sibling_ir_sources(changed)
            assert converted["dependencies"][name][setting] == value
            assert converted != trust_mode, (name, setting)
