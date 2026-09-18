"""Integration controls for manifest integrity and Python optimization handling."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent


class FailClosedControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='mf14-verifier-control-')
        self.package = Path(self.temp.name) / 'package'
        self.verification = self.package / 'verification'
        self.verification.mkdir(parents=True)
        shutil.copytree(PACKAGE / 'source', self.package / 'source')
        for name in ('verify.py', 'input_manifest.json'):
            shutil.copyfile(HERE / name, self.verification / name)
        self.runner = self.verification / 'verify.py'

    def tearDown(self):
        self.temp.cleanup()

    def run_runner(self, flags=(), optimize_env=None):
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        if optimize_env is not None:
            env['PYTHONOPTIMIZE'] = optimize_env
        return subprocess.run([sys.executable, *flags, str(self.runner), '--check-inputs-only'],
                              env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=20)

    def check_rejected(self, result, reason):
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn('FAIL:', result.stdout)
        self.assertIn(reason, result.stdout)
        self.assertNotIn('PASS:', result.stdout)
        self.assertFalse((self.verification / 'reproduction').exists())

    def test_frozen_inputs_accepted(self):
        result = self.run_runner()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('all ten source inputs match', result.stdout)

    def test_seed_mutation_rejected(self):
        path = self.package / 'source/experiments/lower_full49_seed.json'
        raw = path.read_bytes()
        seed = json.loads(raw)
        original = seed['theta_numerators'][0][0].encode()
        replacement = original[:-1] + (b'1' if original[-1:] != b'1' else b'2')
        changed = raw.replace(original, replacement, 1)
        self.assertEqual(len(changed), len(raw))
        self.assertNotEqual(changed, raw)
        path.write_bytes(changed)
        self.check_rejected(self.run_runner(), 'Frozen input hash mismatch')

    def test_manifest_mutation_rejected(self):
        path = self.verification / 'input_manifest.json'
        path.write_bytes(path.read_bytes() + b' ')
        self.check_rejected(self.run_runner(), 'Frozen input manifest hash mismatch')

    def test_unlisted_source_file_rejected(self):
        (self.package / 'source/unreviewed.py').write_text('print("unreviewed")\n')
        self.check_rejected(self.run_runner(), 'file set differs')

    def test_source_symlink_rejected(self):
        path = self.package / 'source/proof.md'
        path.unlink()
        path.symlink_to(PACKAGE / 'source/proof.md')
        self.check_rejected(self.run_runner(), 'Symlink in frozen source')

    def test_optimized_invocations_rejected(self):
        for flag in ('-O', '-OO'):
            with self.subTest(flag=flag):
                self.check_rejected(self.run_runner(flags=(flag,)), 'Optimized Python is refused')

    def test_optimization_environment_rejected(self):
        self.check_rejected(self.run_runner(optimize_env='1'), 'Optimized Python is refused')

    def test_ignore_environment_option_restores_safe_invocation(self):
        result = self.run_runner(flags=('-E',), optimize_env='2')
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('PASS:', result.stdout)


if __name__ == '__main__':
    unittest.main(verbosity=2)
