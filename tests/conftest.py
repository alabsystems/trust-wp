# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Repository-local pytest bootstrap.

The restored Creusot compatibility suite is self-contained.  Do not import the
AI-template fixture facade here: trust-wp does not vendor that facade's runtime
modules, and loading it made the documented plain ``pytest`` entry point fail
before collecting any trust-wp tests.
"""

import sys
from pathlib import Path

# Plain `pytest` does not always seed the repo root on sys.path the same way
# `python -m pytest` does, so make the test package importable up front.
_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
