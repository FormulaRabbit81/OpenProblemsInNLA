"""Replay the bounded AC02/AC03 review in a fresh temporary copy.

Needs Python 3.10+, NumPy and SymPy. Does not run numerical searches,
generators, shell scripts, or incomplete continuation/classification claims.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import zipfile

parser=argparse.ArgumentParser()
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--out',type=Path,required=True)
args=parser.parse_args()
repo=args.repo.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
ref=repo/'references/holden-ac-2026-09-14'
assert (ref/'provenance.json').is_file()
provenance=json.loads((ref/'provenance.json').read_text())
selected=['AC02_updated_research_pack.zip','AC03_updated_research_pack.zip']
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def receipt():
    result={}
    for key in selected:
        for rel,want in provenance[key]['files'].items():
            path=ref/'submitted'/rel
            got=digest(path)
            assert got==want,(rel,got,want)
            result[path.relative_to(repo).as_posix()]=got
    return result
before=receipt()
archive_receipt=[]
for path in sorted((ref/'submitted/AC03_updated_pack/AC03_round3_verified/prior').glob('*.zip')):
    with zipfile.ZipFile(path) as archive:
        assert archive.testzip() is None
        for info in archive.infolist():
            name=PurePosixPath(info.filename)
            assert not name.is_absolute() and '..' not in name.parts
            assert (info.external_attr>>16)&0o170000 != 0o120000
        archive_receipt.append({'path':path.relative_to(repo).as_posix(),'sha256':digest(path),'entries':len(archive.infolist()),'crc_and_safe_paths':True})
results={}
def run(name,command,cwd,success):
    proc=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/name).write_text(proc.stdout)
    assert (proc.returncode==0)==success,(name,proc.returncode)
    results[name]={'returncode':proc.returncode,'expected_success':success}
with tempfile.TemporaryDirectory(prefix='ac02-ac03-review-',dir=out) as work:
    work=Path(work)
    for name in ['AC02_updated_research_pack','AC03_updated_pack']:
        shutil.copytree(ref/'submitted'/name,work/name)
    ac02=work/'AC02_updated_research_pack/round1'
    ac03=work/'AC03_updated_pack/AC03_round3_verified'
    run('ac02-round1-rerun.json',[sys.executable,'code/verify.py'],ac02,True)
    run('ac02-tests.log',[sys.executable,'code/self_tests.py'],ac02,True)
    run('ac03-runner.log',[sys.executable,'code/verify_all.py'],ac03,False)
    child=(ac03/'results/section_geometry_verification.log').read_text()
    assert 'section_geometry.py' in child and 'No such file' in child
    (out/'ac03-first-child.log').write_text(child)
run('independent-checks.log',[sys.executable,str(Path(__file__).with_name('independent_checks.py')),'--repo',str(repo),'--out',str(out)],out,True)
assert receipt()==before
record={'python':sys.version,'reviewed_head':'9bf50028bc30e6cdf78e19089befcb9b9bd6c292','payload_files':before,'all_payload_hashes_match_provenance':True,'source_unchanged':True,'nested_archives':archive_receipt,'outer_zip_hashes_not_independently_checked':{key:provenance[key]['sha256'] for key in selected},'runs':results}
(out/'hash-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'payloads_verified':len(before),'source_unchanged':True,'runs':results},indent=2))
