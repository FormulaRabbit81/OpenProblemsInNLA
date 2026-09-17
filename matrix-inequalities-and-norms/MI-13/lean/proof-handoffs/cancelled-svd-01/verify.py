#!/usr/bin/env python3
"""Read-only source/handoff checker; no compiler or Git."""
from pathlib import Path
import hashlib
import json
import sys

R = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda n: json.loads((R / n).read_text())
m = read('MANIFEST.json')
actual = {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and p != R / 'MANIFEST.json'}
assert set(m['files']) == actual
count = 0
for name, row in m['files'].items():
    assert sha(R / name) == row['sha256'], name
    assert (R / name).stat().st_size == row['bytes'], name
    count += 1
bindings = read('BINDINGS.json')['bindings']
assert len(bindings) == 35
for row in bindings:
    for name in row.get('packet_copies', []):
        assert sha(R / name) == row['sha256'], name
        count += 1
    if '--sources' in sys.argv:
        assert sha(row['source']) == row['sha256'], row['source']
        count += 1
c = read('STATIC-CHECKS.json')
assert c['passed'] == len(c['checks']) == 112 and c['failed'] == 0
assert all(x['pass'] for x in c['checks'])
g = read('SOURCE-GUARD.json')
assert g['unchanged'] and g['before'] == g['after']
h = read('HEADERS.json')
assert h['exact_frozen_headers'] and len(h['contracts']) == 2
assert h['source_sha256'] == sha(R / 'candidate.lean.txt') == m['source_sha256']
assert m['candidate_compilation'] == 'UNRUN_AT_PREPARATION'
assert m['new_independent_proof_approval'] is False
print(json.dumps({'status': 'PASS', 'scope': 'static metadata/hash checks only',
                  'payload_files': len(m['files']), 'bindings': len(bindings),
                  'hash_checks': count, 'manifest_sha256': sha(R / 'MANIFEST.json')}))
