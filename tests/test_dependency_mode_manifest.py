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
TRUST_IR_PATH_DEPENDENCY = {"path": "../trust-ir/crates/trust-ir"}


def _workspace_table(path: Path) -> dict[str, object]:
    manifest = tomllib.loads(path.read_text(encoding="utf-8"))
    return manifest["workspace"]


def test_trust_dependency_mode_matches_root_except_trust_ir_source() -> None:
    standalone = deepcopy(_workspace_table(WORKSPACE_ROOT / "Cargo.toml"))
    trust_mode = _workspace_table(
        WORKSPACE_ROOT / "dependency-modes" / "trust" / "Cargo.toml"
    )

    standalone_dependencies = standalone["dependencies"]
    assert isinstance(standalone_dependencies, dict)
    standalone_dependencies["trust-ir"] = TRUST_IR_PATH_DEPENDENCY

    assert trust_mode == standalone
