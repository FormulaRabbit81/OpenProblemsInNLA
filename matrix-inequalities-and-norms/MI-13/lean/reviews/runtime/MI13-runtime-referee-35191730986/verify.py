#!/usr/bin/env python3
"""Verify this sealed evidence review; no compiler, cache, Git, or network."""
from pathlib import Path
import argparse,hashlib,json
r=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--sources',action='store_true');args=p.parse_args()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=json.loads((r/'MANIFEST.json').read_text())['files']
assert set(files)=={x.relative_to(r).as_posix() for x in r.rglob('*') if x.is_file() and x!=r/'MANIFEST.json'},'inventory'
for rel,h in files.items():assert sha(r/rel)==h,rel
n=0
if args.sources:
    bindings=json.loads((r/'SOURCE-BINDINGS.json').read_text())
    for path,h in bindings.items():assert sha(path)==h,path
    n=len(bindings)
print(json.dumps({'result':'PASS','payloads':len(files),'current_bindings':n,'compiler_or_network_execution':False}))
