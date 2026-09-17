#!/usr/bin/env python3
"""Read immutable public Git tree/blob bytes; never mutate Git or execute Lean."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import base64
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[1]
GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
REPO = 'sidneyholden1/OpenProblemsInNLA'
HEAD = '281f440650d174602120ca9b2b930d38f9fef205'
PREFIX = 'intervals-and-absolute-value-equations/IV-03/lean'
sha = lambda b: hashlib.sha256(b).hexdigest()

def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, path
    else:
        path.write_bytes(data)

def api(endpoint):
    return subprocess.check_output([GH, 'api', 'repos/' + REPO + '/' + endpoint])

tree_id = HEAD
tree_records = []
for label, next_path in [('root', 'intervals-and-absolute-value-equations'),
                         ('category', 'IV-03'), ('problem', 'lean'), ('project', None)]:
    endpoint = 'git/trees/' + tree_id + ('?recursive=1' if next_path is None else '')
    raw = api(endpoint)
    data = json.loads(raw)
    assert not data.get('truncated', False)
    save(HERE / 'source-trees' / (label + '.json'), raw)
    tree_records.append({'label': label, 'endpoint': endpoint, 'sha256': sha(raw), 'returned_sha': data['sha']})
    if next_path is not None:
        entry = next(e for e in data['tree'] if e['path'] == next_path)
        assert entry['type'] == 'tree'
        tree_id = entry['sha']
entries = [e for e in data['tree'] if e['type'] == 'blob']
assert len(entries) == 75

def fetch(entry):
    rel = entry['path']
    blob = json.loads(api('git/blobs/' + entry['sha']))
    assert blob['encoding'] == 'base64' and blob['sha'] == entry['sha']
    contents = base64.b64decode(blob['content'])
    assert len(contents) == blob['size']
    actual_blob = hashlib.sha1(b'blob ' + str(len(contents)).encode() + b'\0' + contents).hexdigest()
    assert actual_blob == entry['sha'], rel
    save(PACKAGE / rel, contents)
    if rel in ['README.md', 'formalization.yaml']:
        save(HERE / 'before' / rel, contents)
    return {'path': rel, 'source_commit': HEAD, 'Git_blob': actual_blob,
            'sha256': sha(contents), 'bytes': len(contents),
            'immutable_source_url': 'https://github.com/' + REPO + '/blob/' + HEAD + '/' + PREFIX + '/' + rel}

with ThreadPoolExecutor(max_workers=4) as pool:
    bindings = list(pool.map(fetch, entries))
save(HERE / 'ORIGINAL-75-INPUTS.json', (json.dumps(sorted(bindings, key=lambda r:r['path']), indent=2) + '\n').encode())
save(HERE / 'SOURCE-TREE-BINDINGS.json', (json.dumps(tree_records, indent=2) + '\n').encode())
print(json.dumps({'immutable_source_commit': HEAD, 'fetched_and_Git_blob_verified_inputs': len(bindings),
                  'package': str(PACKAGE), 'local_Lean': False, 'Git_mutation': False}, indent=2))
