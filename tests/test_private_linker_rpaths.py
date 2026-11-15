"""Inert argv fixtures for private SDK linking; no native runtime claim."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

WRAPPER = Path(__file__).resolve().parents[1] / "scripts/trustc-private-wrapper.sh"


class PrivateLinkerRpaths(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.sdk = self.root / "SDK with spaces"
        self.lib = self.sdk / "lib"
        self.target = self.lib / "rustlib/aarch64-apple-darwin/lib"
        self.target.mkdir(parents=True)
        for directory, name in [(self.lib, "librustc_driver-aaaa.dylib"),
                                (self.target, "librustc_driver-aaaa.dylib"),
                                (self.target, "librustc_middle-bbbb.rmeta"),
                                (self.target, "libstd-cccc.rlib")]:
            (directory / name).touch()
        self.compiler = self.root / "compiler"
        self.compiler.write_text(
            "#!/usr/bin/env python3\nimport json,sys\n"
            f"sdk={str(self.sdk)!r}\ntarget={str(self.target)!r}\n"
            "args=sys.argv[1:]\n"
            "if args==['--print','sysroot']: print(sdk)\n"
            "elif args==['--print','target-libdir']: print(target)\n"
            "elif args==['-vV']: print('commit-hash: '+'a'*40)\n"
            "else: print(json.dumps(args))\n"
        )
        self.compiler.chmod(0o755)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        brew = self.bin / "brew"
        brew.write_text("#!/bin/sh\nprintf '%s\\n' '" + str(self.root / "missing-prefix") + "'\n")
        brew.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ["PATH"])

    def invoke(self, *extra, crate="trust_wp_driver"):
        original = ["--crate-name", crate, "input with spaces.rs", *extra]
        result = subprocess.run([str(WRAPPER), str(self.compiler), *original],
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        args = json.loads(result.stdout)
        self.assertEqual(args[-len(original):], original)
        self.assertIn("-Cprefer-dynamic", args)
        self.assertFalse(any("homebrew" in arg or "missing-prefix" in arg for arg in args))
        return args

    def test_cc_driver_keeps_relative_rpaths_before_private_sdk(self):
        args = self.invoke()
        expected = ["-Clink-arg=-Wl,-rpath,@executable_path/../lib",
                    "-Clink-arg=-Wl,-rpath,@loader_path/../lib",
                    "-Clink-arg=-Wl,-rpath," + str(self.target)]
        self.assertLess(args.index(expected[0]), args.index(expected[1]))
        self.assertLess(args.index(expected[1]), args.index(expected[2]))

    def test_native_darwin_uses_raw_rpath_pairs_and_preserves_spaces(self):
        for crate in ["trust_wp_driver", "trust_wp_rustc"]:
            with self.subTest(crate=crate):
                args = self.invoke("--resource-worker-v2", crate=crate)
                self.assertFalse(any("-Wl," in arg for arg in args))
                self.assertIn("-Clink-arg=" + str(self.target), args)
                first = args.index("-Clink-arg=-rpath")
                self.assertEqual(args[first + 1], "-Clink-arg=@executable_path/../lib")

    def test_explicit_cc_linker_or_flavor_is_preserved(self):
        for override in [["-Clinker=/usr/bin/cc"], ["-C", "linker-flavor=darwin-cc"],
                         ["--codegen", "linker=/usr/bin/cc"],
                         ["--codegen=linker=/usr/bin/cc"],
                         ["--codegen", "linker-flavor=darwin-cc"],
                         ["--codegen=linker-flavor=darwin-cc"],
                         ["-C=linker=/usr/bin/cc"]]:
            with self.subTest(override=override):
                args = self.invoke("--resource-worker-v2", *override)
                self.assertIn("-Clink-arg=-Wl,-rpath,@executable_path/../lib", args)
                self.assertNotIn("-Clink-arg=-rpath", args)

    def test_cross_target_without_optional_native_dirs_keeps_only_target_paths(self):
        text = WRAPPER.read_text()
        functions = []
        for name in ["is_driver_crate", "emit_and_exec"]:
            start = text.index(name + "() {")
            functions.append(text[start:text.index("\n}\n", start) + 3])
        private = self.root / "target-private"
        std = self.root / "target-std"
        private.mkdir()
        std.mkdir()
        setup = '\nRUSTC="$1"; SR="$2"; DRIVER_SUFFIX=dylib; IS_CROSS=1; DRIVER_CRATES=trust_wp_driver\n'
        command = '\nemit_and_exec "$2" "$2/host-llvm" "$2/host-native" "$2/host-private" "$2/host-std" "$3" "$4" "$2/missing-llvm" "$2/missing-native" --crate-name trust_wp_driver --resource-worker-v2\n'
        result = subprocess.run(["/bin/bash", "-eu", "-c", "\n".join(functions) + setup + command,
                                 "inert-test", str(self.compiler), str(self.sdk), str(private), str(std)],
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        args = json.loads(result.stdout)
        self.assertIn("-Clink-arg=" + str(private), args)
        self.assertIn("-Clink-arg=" + str(std), args)
        self.assertFalse(any("host-private" in arg or "host-std" in arg or "missing-" in arg for arg in args))
        self.assertNotIn("", args)


if __name__ == "__main__":
    unittest.main()
