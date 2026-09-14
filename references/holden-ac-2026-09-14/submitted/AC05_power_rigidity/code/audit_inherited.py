#!/usr/bin/env python3
"""Replay the unchanged inherited archive in a temporary directory."""
from pathlib import Path
import hashlib, json, subprocess, sys, tempfile, zipfile
ROOT=Path(__file__).resolve().parents[1]
archive=ROOT/'baseline'/'AC05_rank_speedup.zip'
with tempfile.TemporaryDirectory(prefix='ac05-inherited-') as tmp:
    tmp=Path(tmp)
    with zipfile.ZipFile(archive) as z:
        for entry in z.infolist():
            target=(tmp/entry.filename).resolve()
            if not target.is_relative_to(tmp.resolve()):raise ValueError('Unsafe archive member')
        z.extractall(tmp)
    candidates=list(tmp.rglob('code/replay_certificates.py'))
    if len(candidates)!=1:raise ValueError('Ambiguous inherited checker path')
    proc=subprocess.run([sys.executable,str(candidates[0])],cwd=candidates[0].parents[1],capture_output=True,text=True)
    (ROOT/'results'/'inherited_replay.log').write_text(proc.stdout+proc.stderr)
    if proc.returncode:raise RuntimeError('Inherited checker failed; see log')
    out={'status':'PASS','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
         'scope':'Inherited standard-library finite-certificate replay only; not a new audit of all geometric proofs.'}
    (ROOT/'results'/'inherited_audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))
