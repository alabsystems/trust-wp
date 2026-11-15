"""Stable native units do not acquire the driver's rustc-private overlay."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


class NativeFacadeWrapperTests(unittest.TestCase):
    def test_nonprivate_invocations_keep_the_selected_compiler_and_arguments(self):
        wrapper = Path(__file__).resolve().parents[1] / "scripts/trustc-private-wrapper.sh"
        with tempfile.TemporaryDirectory() as directory:
            compiler = Path(directory) / "compiler"
            compiler.write_text("#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv[1:]))\n")
            compiler.chmod(0o755)
            for arguments in (["-vV"], ["--crate-name", "trust_wp_lib", "input with spaces.rs"],
                              ["--crate-name=trust_wp_core", "--emit=metadata"]):
                result = subprocess.run([str(wrapper), str(compiler), *arguments],
                                        text=True, capture_output=True, check=True)
                self.assertEqual(json.loads(result.stdout), arguments)

    def test_driver_still_requires_the_selected_compiler_private_sdk(self):
        wrapper = Path(__file__).resolve().parents[1] / "scripts/trustc-private-wrapper.sh"
        with tempfile.TemporaryDirectory() as directory:
            compiler = Path(directory) / "compiler"
            compiler.write_text("#!/bin/sh\nexit 29\n")
            compiler.chmod(0o755)
            for spelling in (["--crate-name", "trust_wp_driver"], ["--crate-name=trust_wp_rustc"]):
                result = subprocess.run([str(wrapper), str(compiler), *spelling], capture_output=True)
                self.assertEqual(result.returncode, 29)


if __name__ == "__main__":
    unittest.main()
