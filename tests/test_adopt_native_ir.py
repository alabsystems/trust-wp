"""Transaction boundaries; native source behavior is checked by Rust consumers."""
import importlib.util
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import zlib
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('adopt', Path(__file__).resolve().parents[1] / 'scripts/adopt_native_ir.py')
adopt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adopt)


class AdoptionTests(unittest.TestCase):
    def test_graph_rejects_unrelated_edges_and_checksums(self):
        before = ('[[package]]\nname="a"\nversion="1"\nsource="git+' + adopt.IR + '?rev=old#old"\nchecksum="same"\ndependencies=["b"]\n').encode()
        moved = before.replace(b'rev=old#old', b'rev=new#new')
        self.assertEqual(adopt.lock_graph(before, [('old', 'new')]), adopt.lock_graph(moved))
        for changed in (moved.replace(b'"b"', b'"c"'), moved.replace(b'same', b'other')):
            self.assertNotEqual(adopt.lock_graph(before, [('old', 'new')]), adopt.lock_graph(changed))

    def test_idempotent_graph_move_preserves_leaf_nodes(self):
        leaf = b'[[package]]\nname="leaf"\nversion="1"\n'
        self.assertEqual(adopt.lock_graph(leaf, [('a' * 40, 'a' * 40)]), adopt.lock_graph(leaf))

    def test_immutable_revision_required(self):
        for value in ('main', 'abc', 'a' * 39, 'A' * 40):
            with self.assertRaises(RuntimeError):
                adopt.exact(value)

    def test_conflicting_clean_owners_refuse(self):
        def manifest(store, revision, path):
            rev = 'a' * 40 if 'trust-ir-build' in path else 'b' * 40
            return '[dependencies]\nclean-kernel = {git="' + adopt.CLEAN + '",rev="' + rev + '"}'
        with patch.object(adopt, 'blob', side_effect=manifest):
            with self.assertRaisesRegex(RuntimeError, 'one exact Clean'):
                adopt.clean_owner(None, 'a' * 40)

    def test_producer_failure_restores_every_governed_byte(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'trust-wp'
            root.mkdir()
            sibling_revisions = {}
            for name in ('ay', 'clean'):
                sibling = root.parent / name
                subprocess.run(['git', 'init', '-q', sibling], check=True)
                subprocess.run(['git', '-C', sibling, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                                'commit', '--allow-empty', '-qm', 'source'], check=True)
                sibling_revisions[name] = subprocess.check_output(['git', '-C', sibling, 'rev-parse', 'HEAD'], text=True).strip()
            subprocess.run(['git', 'init', '-q', root], check=True)
            old = 'a' * 40
            new = 'b' * 40
            manifest = '[workspace.dependencies]\n' + '\n'.join(
                p + ' = {git="' + adopt.IR + '", rev = "' + old + '"}' for p in adopt.PROVIDERS)
            for name, data in [('Cargo.toml', manifest), ('Cargo.lock', 'original lock'),
                               ('dependency-modes/trust/Cargo.lock', 'original importer'),
                               ('dependency-modes/LIVE_DEPENDS.lock', '\n'.join(
                                   f'{name} main {rev}' for name, rev in {**sibling_revisions, 'trust-ir': old}.items()) + '\n')]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(data)
            (root / 'dependency-modes/trust/Cargo.toml').write_text('[workspace.dependencies]\n' + '\n'.join(
                p + ' = {path="../trust-ir/crates/' + p + '"}' for p in adopt.PROVIDERS))
            subprocess.run(['git', 'add', '.'], cwd=root, check=True)
            subprocess.run(['git', '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                            'commit', '-qm', 'fixture'], cwd=root, check=True)
            originals = {p: (root / p).read_bytes() for p in adopt.OWNED}
            targo = root / 'targo'
            targo.write_text('#!/bin/sh\nprintf "targo test\\n"\n')
            targo.chmod(0o755)
            def fail_producer(*args):
                (root / 'Cargo.lock').write_text('partial producer write')
                raise subprocess.CalledProcessError(101, 'metadata')
            real_run = subprocess.run
            with patch.object(adopt, 'authority', return_value=root), \
                 patch.object(adopt, 'clean_owner', return_value='c' * 40), \
                 patch.object(adopt, 'metadata', side_effect=fail_producer), \
                 patch.object(adopt.subprocess, 'run', wraps=subprocess.run) as invoked:
                # Only the main ancestry command is supplied by the authority fixture.
                def run_command(argv, **kwargs):
                    if 'merge-base' in argv:
                        return subprocess.CompletedProcess(argv, 0)
                    return real_run(argv, **kwargs)
                invoked.side_effect = run_command
                with self.assertRaises(subprocess.CalledProcessError):
                    adopt.transaction(root, new, targo, root)
            self.assertEqual(originals, {p: (root / p).read_bytes() for p in adopt.OWNED})


class GitAuthorityIsolationTests(unittest.TestCase):
    def test_external_and_cached_grafts_cannot_admit_an_unrelated_root(self):
        git = adopt.shutil.which('git')
        self.assertIsNotNone(git)
        base = Path(tempfile.gettempdir()) / '.ubd'
        base.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base, prefix='wp-authority-graft-') as directory:
            root = Path(directory)
            safe = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
            safe.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1')
            objects = []
            def obj(kind, data):
                raw = kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data
                identity = hashlib.sha1(raw).hexdigest()
                objects.append((identity, zlib.compress(raw)))
                return identity
            tree = obj('tree', b'')
            def commit(message):
                return obj('commit', (f'tree {tree}\nauthor Fixture <fixture@example.invalid> 1 +0000\n'
                    f'committer Fixture <fixture@example.invalid> 1 +0000\n\n{message}\n').encode())
            main, unrelated = commit('main'), commit('unrelated')
            template = root / 'template'
            (template / 'info').mkdir(parents=True)
            graft = template / 'info/grafts'
            graft.write_text(f'{main} {unrelated}\n')
            global_config = root / 'global-config'
            global_config.write_text(f'[init]\n templateDir = {template}\n')
            real_run = adopt.run
            def transport(argv, cwd=None):
                if str(argv[0]) == 'agh':
                    if list(argv[1:3]) not in (['repo', 'fetch-main'], ['repo', 'fetch']):
                        raise AssertionError('unexpected authority transport')
                    store = Path(argv[4])
                    for identity, data in objects:
                        target = store / 'objects' / identity[:2] / identity[2:]
                        target.parent.mkdir(exist_ok=True)
                        target.write_bytes(data)
                    real_run([git, '-C', store, 'update-ref', 'refs/agh/fetched-main', main])
                    return ''
                return real_run(argv, cwd)
            poisoned = {'GIT_GRAFT_FILE': str(graft), 'GIT_TEMPLATE_DIR': str(template),
                        'GIT_CONFIG_GLOBAL': str(global_config), 'GIT_NO_REPLACE_OBJECTS': '1'}
            for cached in (False, True):
                with self.subTest(cached=cached):
                    cache = root / ('cached' if cached else 'fresh')
                    cache.mkdir()
                    store = cache / 'trust-ir'
                    if cached:
                        subprocess.run([git, 'init', '--bare', '--quiet', '--template=', store],
                                       env=safe, check=True)
                        # A store left by the old template-bearing initializer.
                        (store / 'info').mkdir(exist_ok=True)
                        (store / 'info/grafts').write_text(graft.read_text())
                    with patch.dict(os.environ, poisoned), patch.object(adopt, 'run', side_effect=transport):
                        with self.assertRaises(subprocess.CalledProcessError):
                            adopt.authority(cache, 'trust-ir', unrelated)
                        self.assertEqual(adopt.authority(cache, 'trust-ir', main), store)
                    if not cached:
                        self.assertFalse((store / 'info/grafts').exists())
                    control_env = safe | {'GIT_NO_REPLACE_OBJECTS': '1'}
                    if cached:
                        self.assertEqual((store / 'info/grafts').read_text(), graft.read_text())
                    else:
                        control_env['GIT_GRAFT_FILE'] = str(graft)
                    control = subprocess.run([git, '-C', store, 'merge-base', '--is-ancestor',
                                              unrelated, 'refs/agh/fetched-main'], env=control_env,
                                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    self.assertEqual(control.returncode, 0, control.stderr)

    def test_subprocess_policy_replaces_ambient_git_inputs_with_neutral_values(self):
        names = {'GIT_GRAFT_FILE', 'GIT_SHALLOW_FILE', 'GIT_TEMPLATE_DIR', 'GIT_NAMESPACE',
                 'GIT_DEFAULT_HASH', 'GIT_DEFAULT_REF_FORMAT', 'GIT_CONFIG_GLOBAL',
                 'GIT_CONFIG_SYSTEM', 'GIT_CONFIG_COUNT', 'GIT_DIR', 'GIT_WORK_TREE',
                 'GIT_COMMON_DIR', 'GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY',
                 'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_REPLACE_REF_BASE'}
        with patch.dict(os.environ, {name: 'poison' for name in names}), \
                patch.object(adopt.subprocess, 'check_output', return_value='ok') as called:
            adopt.run(['git', 'rev-parse', 'HEAD'])
        environment = called.call_args.kwargs.get('env', {})
        self.assertFalse((names - {'GIT_CONFIG_GLOBAL', 'GIT_GRAFT_FILE'}).intersection(environment))
        self.assertEqual(environment.get('GIT_CONFIG_GLOBAL'), os.devnull)
        self.assertEqual(environment.get('GIT_GRAFT_FILE'), os.devnull)
        self.assertEqual(environment.get('GIT_CONFIG_NOSYSTEM'), '1')
        self.assertEqual(environment.get('GIT_NO_REPLACE_OBJECTS'), '1')
        self.assertEqual(environment.get('GIT_NO_LAZY_FETCH'), '1')


class MetadataSnapshotTests(unittest.TestCase):
    def export(self, files, check):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'authority'
            subprocess.run(['git', 'init', '-q', root], check=True)
            for name, data in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                if isinstance(data, tuple):
                    path.symlink_to(data[0])
                else:
                    path.write_bytes(data)
            subprocess.run(['git', '-C', root, 'add', '.'], check=True)
            subprocess.run(['git', '-C', root, '-c', 'user.name=Test',
                            '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'inputs'], check=True)
            revision = subprocess.check_output(['git', '-C', root, 'rev-parse', 'HEAD'], text=True).strip()
            # The exporter must consume immutable objects, not this checkout.
            (root / 'Cargo.toml').write_text('not the authenticated manifest')
            destination = Path(directory) / 'metadata'
            check(root, revision, destination)

    def fixture(self):
        return {'Cargo.toml': b'[workspace]\nmembers=["crates/a"]\n',
                'crates/a/Cargo.toml': b'[package]\nname="a"\nversion="0.1.0"\n',
                'crates/a/src/lib.rs': b'pub fn a() {}\n',
                'reports/history/large.bin': b'historical proof bytes',
                '.gitattributes': b'crates/a/src/lib.rs export-ignore\n'}

    def test_complete_non_report_tree_uses_exact_objects_even_with_archive_attributes(self):
        files = self.fixture()
        files['crates/a/implicit/tests.rs'] = b'implicit target or source input\x00\xff'
        def check(root, revision, destination):
            count = adopt.export_metadata_tree(root, revision, destination)
            expected = {name: data for name, data in files.items() if not name.startswith('reports/')}
            self.assertEqual(count, len(expected))
            self.assertEqual({str(p.relative_to(destination)): p.read_bytes()
                              for p in destination.rglob('*') if p.is_file()}, expected)
            self.assertFalse((destination / 'reports').exists())
        self.export(files, check)

    def test_report_dependency_target_and_parent_normalization_refuse(self):
        for declaration in (b'\n[dependencies]\nhistory={path="../../reports/history"}\n',
                            b'\n[lib]\npath="../../reports/history/large.bin"\n',
                            b'\n[package.metadata]\nother="reports/history/large.bin"\n'):
            with self.subTest(declaration=declaration):
                files = self.fixture()
                files['crates/a/Cargo.toml'] += declaration
                self.export(files, lambda *args: self.assertRaisesRegex(
                    RuntimeError, 'omitted reports', adopt.export_metadata_tree, *args))

    def test_workspace_glob_cannot_silently_remove_report_package(self):
        files = self.fixture()
        files['Cargo.toml'] = b'[workspace]\nmembers=["*"]\n'
        files['reports/history/Cargo.toml'] = files['crates/a/Cargo.toml']
        self.export(files, lambda *args: self.assertRaisesRegex(
            RuntimeError, 'glob reaches omitted reports', adopt.export_metadata_tree, *args))

    def test_config_included_report_and_target_refuse(self):
        for config in (b'include=["../reports/history/config.toml"]\n',
                       b'[build]\ntarget="reports/custom-target.json"\n'):
            with self.subTest(config=config):
                files = self.fixture()
                files['.cargo/config.toml'] = config
                self.export(files, lambda *args: self.assertRaisesRegex(
                    RuntimeError, 'omitted reports', adopt.export_metadata_tree, *args))

    def test_config_paths_and_recursive_includes_use_distinct_cargo_bases(self):
        files = self.fixture()
        files['.cargo/config.toml'] = b'include=["shared.toml",{path="optional.toml",optional=true}]\n'
        files['.cargo/shared.toml'] = b'include=[{path="nested.toml"}]\n[source.vendor]\ndirectory="vendor"\n'
        files['.cargo/nested.toml'] = b'[source.more]\ndirectory="other-vendor"\n'
        files['vendor/item'] = b'actual config-relative input'
        files['other-vendor/item'] = b'actual recursive input'
        self.export(files, lambda *args: adopt.export_metadata_tree(*args))
        files['.cargo/nested.toml'] = b'[source.more]\ndirectory="reports/history"\n'
        self.export(files, lambda *args: self.assertRaisesRegex(
            RuntimeError, 'omitted reports', adopt.export_metadata_tree, *args))

    def test_config_include_cycle_and_missing_required_include_refuse(self):
        for second in (b'include=["config.toml"]\n', b'include=["missing.toml"]\n'):
            with self.subTest(second=second):
                files = self.fixture()
                files['.cargo/config.toml'] = b'include=["second.toml"]\n'
                files['.cargo/second.toml'] = second
                self.export(files, lambda *args: self.assertRaisesRegex(
                    RuntimeError, 'cyclic|missing', adopt.export_metadata_tree, *args))

    def test_non_report_declared_inputs_are_retained_and_missing_or_escaped_inputs_refuse(self):
        files = self.fixture()
        files['crates/a/Cargo.toml'] += b'build="build.rs"\nreadme="../../README.md"\n'
        files['crates/a/build.rs'] = b'fn main() {}'
        files['README.md'] = b'input'
        self.export(files, lambda *args: adopt.export_metadata_tree(*args))
        for path in ('missing.rs', '../../../ambient.rs'):
            with self.subTest(path=path):
                files['crates/a/Cargo.toml'] = b'[package]\nname="a"\nversion="0.1.0"\nbuild="' + path.encode() + b'"\n'
                self.export(files, lambda *args: self.assertRaisesRegex(
                    RuntimeError, 'missing|escapes', adopt.export_metadata_tree, *args))

    def test_symlink_to_omitted_or_ambient_source_refuses(self):
        for target in ('../../reports/history/large.bin', '/tmp/ambient'):
            with self.subTest(target=target):
                files = self.fixture()
                files['crates/a/linked.rs'] = (target,)
                self.export(files, lambda *args: self.assertRaisesRegex(
                    RuntimeError, 'symlink or gitlink', adopt.export_metadata_tree, *args))


if __name__ == '__main__':
    unittest.main()
