#!/usr/bin/env python3
"""Read-only source/hash audit. Does not invoke Lean or establish a proof."""
import hashlib
import json
import re
from pathlib import Path

packet = Path(__file__).resolve().parent
workspace = packet.parent.parent
mathlib = Path('/private/tmp/nla-lean-local-shared-20260916/.lake/packages/mathlib')


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
    assert digest(mathlib / item['path']) == item['sha256'], item['path']
    snapshot = Path(item['snapshot'])
    assert digest(snapshot) == item['sha256'], str(snapshot)
    if 'inherited_record' in item:
        assert digest(Path(item['inherited_record'])) == item['inherited_record_sha256']

source = workspace / 'NLA/MI13/OperatorNorm.lean'
assert source.read_bytes() == (packet / 'sources/OperatorNorm.lean.txt').read_bytes()
src = source.read_text()
challenge = (workspace / 'Challenge.lean').read_text()
pattern = r'theorem operator_norm_semantics\b.*?:= by'
header = re.search(pattern, src, re.S).group(0)
assert header == re.search(pattern, challenge, re.S).group(0)
assert header == json.loads((packet / 'EXACT-HEADER.json').read_text())['header']
assert re.findall(r'^import (\S+)', src, re.M) == ['NLA.MI13.SingularSemantics']
code = re.sub(r'/\-.*?\-/', '', src, flags=re.S)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code)
assert '#assert_trust kernel operator_norm_semantics' in code
assert '#print axioms operator_norm_semantics' in code
assert 'set_option leancert.trust "kernel"' in code
assert re.findall(r'^theorem (\w+)', code, re.M) == ['operator_norm_semantics']
assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats|debug|trace)', code)

freeze = json.loads((workspace / 'STATEMENT-FREEZE.json').read_text())
assert len(freeze['frozen_files']) == 13
for rel, sha in freeze['frozen_files'].items():
    assert digest(workspace / rel) == sha, rel

print('PASS: source/hash/header audit only; 13 frozen inputs unchanged; '
      '1 exact contract; 12 pinned primary files. Lean/Comparator unrun.')
