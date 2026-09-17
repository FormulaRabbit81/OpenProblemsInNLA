#!/usr/bin/env python3
"""Read-only source/hash audit. Does not invoke Lean or prove any theorem."""
import hashlib
import json
import re
from pathlib import Path

packet = Path(__file__).resolve().parent
workspace = packet.parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((packet / 'MANIFEST.json').read_text())
actual_files = {str(p.relative_to(packet)) for p in packet.rglob('*')
                if p.is_file() and p.name != 'MANIFEST.json'}
assert actual_files == set(manifest['files'])
for rel, sha in manifest['files'].items():
    assert digest(packet / rel) == sha, rel

for item in json.loads((packet / 'INPUT-BINDINGS.json').read_text())['inputs']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']

for item in json.loads((packet / 'PRIMARY-BINDINGS.json').read_text())['primary_sources']:
    path = Path(item['path'])
    assert digest(path) == item['sha256'], str(path)
    lines = path.read_text().splitlines()
    for excerpt in item['excerpts']:
        actual = '\n'.join(lines[excerpt['first_line'] - 1:excerpt['last_line']]) + '\n'
        assert actual == excerpt['text'], str(path)
        assert hashlib.sha256(actual.encode()).hexdigest() == excerpt['sha256']

for item in json.loads((packet / 'IMPORT-AVAILABILITY.json').read_text())['imports']:
    for artifact in item['cache_artifacts']:
        path = Path(artifact['path'])
        assert path.is_file() == artifact['exists'], str(path)
        if artifact['exists']:
            assert digest(path) == artifact['sha256'], str(path)

source = workspace / 'NLA/MI13/Padding.lean'
assert source.read_bytes() == (packet / 'sources/Padding.lean.txt').read_bytes()
src = source.read_text()
challenge = (workspace / 'Challenge.lean').read_text()
headers = json.loads((packet / 'EXACT-HEADERS.json').read_text())
names = ['padding_product', 'padding_norms', 'padding_singular_values']
assert set(headers) == set(names)
for name in names:
    pattern = r'theorem ' + name + r'\b.*?:= by'
    header = re.search(pattern, src, re.S).group(0)
    assert header == re.search(pattern, challenge, re.S).group(0), name
    assert header == headers[name]['header'], name
    assert hashlib.sha256(header.encode()).hexdigest() == headers[name]['sha256']
    assert '#print axioms ' + name in src
    assert '#assert_trust kernel ' + name in src

assert re.findall(r'^import (\S+)', src, re.M) == [
    'NLA.MI13.Frobenius', 'NLA.MI13.OperatorNorm', 'Mathlib.Data.List.GetD',
    'Mathlib.LinearAlgebra.Charpoly.ToMatrix', 'Mathlib.LinearAlgebra.Matrix.Reindex']
code = re.sub(r'/\-.*?\-/', '', src, flags=re.S)
code = re.sub(r'--[^\n]*', '', code)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code)
assert set(re.findall(r'^theorem (\w+)', code, re.M)) == set(names)
assert 'set_option leancert.trust "kernel"' in code
assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats|debug|trace)', code)

freeze = json.loads((workspace / 'STATEMENT-FREEZE.json').read_text())
assert len(freeze['frozen_files']) == 13
for rel, sha in freeze['frozen_files'].items():
    assert digest(workspace / rel) == sha, rel

static = json.loads((packet / 'STATIC-CHECKS.json').read_text())
assert static['source_sha256'] == digest(source)
assert static['all_compiler_and_trust_runs'] == 'UNRUN'
assert static['linux_comparator'] == 'UNRUN'
print('PASS: source/hash/header audit only; three exact frozen padding contracts; '
      '13 frozen files unchanged; 26 local pinned API sources; Lean/Comparator unrun.')
