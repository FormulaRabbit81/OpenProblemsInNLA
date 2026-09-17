#!/usr/bin/env python3
"""Read-only repair audit; never invokes Lean or establishes theorem validity."""
import difflib
import hashlib
import json
import re
from pathlib import Path

packet = Path(__file__).resolve().parent
workspace = packet.parent.parent
original = packet.parent / 'padding-02'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((packet / 'MANIFEST.json').read_text())
actual = {str(p.relative_to(packet)) for p in packet.rglob('*')
          if p.is_file() and p.name != 'MANIFEST.json'}
assert actual == set(manifest['files'])
for rel, expected in manifest['files'].items():
    assert digest(packet / rel) == expected, rel

before = json.loads((packet / 'BEFORE-BINDINGS.json').read_text())
assert digest(original / 'MANIFEST.json') == before['original_manifest_sha256']
assert json.loads((original / 'MANIFEST.json').read_text())['files'] == before['original_files']
for rel, expected in before['original_files'].items():
    assert digest(original / rel) == expected, rel

for item in json.loads((packet / 'INPUT-BINDINGS.json').read_text())['inputs']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']
for item in json.loads((packet.parent / 'padding-01/PRIMARY-BINDINGS.json').read_text())['primary_sources']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']

freeze = json.loads((workspace / 'STATEMENT-FREEZE.json').read_text())
assert len(freeze['frozen_files']) == 13
for rel, expected in freeze['frozen_files'].items():
    assert digest(workspace / rel) == expected, rel

source = workspace / 'NLA/MI13/Padding.lean'
assert source.read_bytes() == (packet / 'sources/Padding.lean.txt').read_bytes()
old = (original / 'sources/Padding.lean.txt').read_text()
new = source.read_text()
expected_diff = ''.join(difflib.unified_diff(
    old.splitlines(True), new.splitlines(True),
    fromfile='padding-02/Padding.lean', tofile='padding-03/Padding.lean'))
assert expected_diff == (packet / 'SOURCE.diff').read_text()
assert 'gram_charpoly_eq_matrix' not in new
assert re.findall(r'^import (\S+)', new, re.M) == [
    'NLA.MI13.UnitaryInvariance', 'Mathlib.Data.List.GetD',
    'Mathlib.LinearAlgebra.Matrix.Reindex']
names = ['padding_product', 'padding_norms', 'padding_singular_values']
headers = json.loads((packet / 'EXACT-HEADERS.json').read_text())
challenge = (workspace / 'Challenge.lean').read_text()
for name in names:
    pattern = r'theorem ' + name + r'\b.*?:= by'
    header = re.search(pattern, new, re.S).group(0)
    assert header == re.search(pattern, challenge, re.S).group(0), name
    assert header == headers[name]['header'], name
    assert hashlib.sha256(header.encode()).hexdigest() == headers[name]['sha256']
    assert '#print axioms ' + name in new
    assert '#assert_trust kernel ' + name in new
code = re.sub(r'/\-.*?\-/', '', new, flags=re.S)
code = re.sub(r'--[^\n]*', '', code)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code)
assert set(re.findall(r'^theorem (\w+)', code, re.M)) == set(names)
assert 'set_option leancert.trust "kernel"' in code
assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats|debug|trace)', code)

failure = json.loads((packet / 'FAILURE-BINDING.json').read_text())
receipt = json.loads((packet / 'local49/RECEIPT.json').read_text())
assert digest(packet / 'local49/RECEIPT.json') == failure['receipt_sha256']
assert digest(Path(failure['receipt_path'])) == failure['receipt_sha256']
command = next(c for c in receipt['commands'] if c['module'] == 'NLA.MI13.Padding')
assert command == failure['padding_command']
assert command['source_sha256'] == digest(original / 'sources/Padding.lean.txt')
assert command['log_sha256'] == digest(packet / 'local49/NLA.MI13.Padding.log')
assert command['exit_code'] == 1 and command['output_sha256'] is None
assert failure['retry_status'] == 'UNRUN'
print('PASS: repair source/hash/header audit; original packet and 13 frozen files unchanged; '
      'actual local49 failure bound; repaired Lean/Comparator checks unrun.')
