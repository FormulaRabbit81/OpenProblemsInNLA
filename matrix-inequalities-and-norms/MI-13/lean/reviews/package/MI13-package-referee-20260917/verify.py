#!/usr/bin/env python3
"""Verify this exact review packet; optionally authenticate current bindings.

Does not execute the package preparer, audit.py, Lean, Lake, Git or network.
Historical pass1 bindings are preserved but are not current-source assertions.
"""
from pathlib import Path
import argparse, hashlib, json

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--sources', action='store_true')
args = parser.parse_args()
digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
manifest = json.loads((root/'MANIFEST.json').read_text())
files = manifest['files']
actual = {str(p.relative_to(root)) for p in root.rglob('*')
          if p.is_file() and p != root/'MANIFEST.json'}
assert actual == set(files), 'Review inventory differs'
for rel, expected in files.items():
    assert digest(root/rel) == expected, rel
count = 0
if args.sources:
    bindings = json.loads((root/'BINDINGS.json').read_text())
    for path, expected in bindings.items():
        assert digest(path) == expected, path
    count = len(bindings)
print(json.dumps({'result': 'PASS', 'payloads': len(files),
                  'current_bindings_checked': count,
                  'compiler_or_network_executed': False}))
