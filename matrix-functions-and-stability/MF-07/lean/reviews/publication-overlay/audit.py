#!/usr/bin/env python3
"""Read-only independent publication audit; writes this review packet only."""
import difflib
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import zipfile

sys.dont_write_bytecode = True
R = Path(__file__).resolve().parent
B = Path('/tmp/nla-lean-next-20260915')
P = B / 'MF07-publication-private-35172783207'
W = Path('/private/tmp/nla-lean-next-mf07-worktree')
RUN = B / 'canonical-runs/MF07-35172783207'
REV = 'b2b9acc83ad7d6b7d3888de8390475a30c720af8'
PROJECT = 'matrix-functions-and-stability/MF-07/lean'
CANON = 'matrix-functions-and-stability/MF-07/README.md'
checks = []
bindings = {}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def check(cond, label):
    assert cond, label
    checks.append(label)

def bound(path, expected=None):
    path = Path(path)
    data = path.read_bytes()
    h = sha(data)
    if expected:
        check(h == expected, 'hash ' + str(path))
    bindings[str(path)] = h
    return data

def load(path, expected=None):
    return json.loads(bound(path, expected))

def write(name, obj):
    (R / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

def git(path):
    return subprocess.check_output(['git', '-C', str(W), 'show', REV + ':' + path])

manifest = load(P / 'MANIFEST.json', 'bb2d8771b8212faba706618f1abef7d07156505413d5e0c01d7d9d28d205be74')
for path, h in manifest['files'].items():
    bound(P / path, h)
check({str(f.relative_to(P)) for f in P.rglob('*') if f.is_file()} == set(manifest['files']) | {'MANIFEST.json'}, 'exact immutable proposal inventory')
t = load(P / 'TRANSITION.json', '4662fdadfbb8305ae8f1a0be423dc4d50644166659688a26b5c611dd4b58ff7a')
check(t['proof_commit'] == REV and t['run'] == 35172783207, 'literal proof/run identities')
check(len(t['protected_original_inputs']) == 297 and len(t['protected_math_files']) == 21, '297 input and21 proof count')

# Read all committed project blobs in one read-only Git batch. The coordinator may
# edit the physical worktree concurrently; no original-byte assertion uses it.
tree = subprocess.check_output(['git', '-C', str(W), 'ls-tree', '-rz', REV, '--', PROJECT])
rows = []
for row in tree.split(b'\0'):
    if not row:
        continue
    meta, path = row.split(b'\t', 1)
    mode, typ, oid = meta.decode().split()
    check(typ == 'blob' and mode in ['100644', '100755'], 'ordinary project blob ' + path.decode())
    rows.append((path.decode()[len(PROJECT)+1:], oid))
proc = subprocess.run(['git', '-C', str(W), 'cat-file', '--batch'],
                      input=('\n'.join(oid for _,oid in rows)+'\n').encode(), stdout=subprocess.PIPE, check=True)
stream = io.BytesIO(proc.stdout)
base = {}
for rel, oid in rows:
    head = stream.readline().decode().split()
    check(head[:2] == [oid, 'blob'], 'Git batch header ' + rel)
    data = stream.read(int(head[2]))
    check(stream.read(1) == b'\n', 'Git batch framing ' + rel)
    base[rel] = data
check(not stream.read(), 'no extra Git batch payload')
check(set(base) == set(t['protected_original_inputs']), 'literal exact297 input paths')
for rel, data in base.items():
    check(sha(data) == t['protected_original_inputs'][rel], 'literal protected input ' + rel)

# Original author bindings under the now-mutable worktree are interpreted at
# their recorded literal proof commit. External immutable packets remain direct.
for path, h in load(P / 'BINDINGS.json').items():
    src = Path(path)
    if src.is_relative_to(W):
        rel = str(src.relative_to(W))
        data = base[rel[len(PROJECT)+1:]] if rel.startswith(PROJECT+'/') else git(rel)
        check(sha(data) == h, 'author origin at literal proof commit ' + rel)
    else:
        bound(src, h)

for path, rec in t['before'].items():
    if rec is None:
        continue
    data = git(path)
    check(sha(data) == rec['sha256'], 'before literal ' + path)
    check(bound(P / 'before' / path) == data, 'retained before bytes ' + path)
for path, rec in t['overlay'].items():
    check(sha(bound(P / 'overlay' / path)) == rec['sha256'], 'overlay hash ' + path)
check(set(t['overlay']) == {str(f.relative_to(P/'overlay')) for f in (P/'overlay').rglob('*') if f.is_file()}, 'exact38 overlay paths')
check(not any(p.endswith('.lean') or p.startswith(('tools/', '.github/')) or p.endswith('problem_ids.json') for p in t['overlay']), 'no proof/checker/workflow/registry overlay')

candidate = dict(base)
for path in t['overlay']:
    if path.startswith(PROJECT+'/'):
        candidate[path[len(PROJECT)+1:]] = (P / 'overlay' / path).read_bytes()
modified = sorted(rel for rel in base if candidate[rel] != base[rel])
check(modified == ['PUBLICATION-EVIDENCE.json', 'README.md', 'formalization.yaml', 'reviews/INDEX.json'], 'only four existing project documentation inputs modified')
for rel, h in t['protected_math_files'].items():
    check(sha(base[rel]) == h and candidate[rel] == base[rel], 'unchanged proof source ' + rel)
for rel in base:
    if rel.startswith('statement-audit/frozen-35064080581/snapshots/'):
        check(candidate[rel] == base[rel], 'unchanged frozen snapshot ' + rel)
local = load(B/'MF07-LOCAL-DEVELOPMENT-ACCEPTANCE.json', '4ce2483aa1909c5a319d87c734bf6ec9d173071b239b6a8a3f159ba46b00c919')
for rel, h in local['accepted_source_sha256'].items():
    target = 'Solution.lean' if rel.endswith('/Complete.lean') else rel
    check(sha(base[target]) == h, 'accepted local proof continuation ' + target)

runtime = P/'overlay'/PROJECT/'verification/linux-35172783207'
actual_result = load(runtime/'result.json')
check(actual_result['repository_commit'] == REV and actual_result['result'] == 'comparator-accepted', 'actual result accepts literal proof')
check(actual_result['input_sha256'] == t['protected_original_inputs'], 'all297 actual receipt inputs')
config = json.loads(base['comparator.json'])
check(actual_result['config'] == config and len(config['theorem_names']) == 18, 'actual exact18 contracts')
root = load(runtime/'ROOT-AUDIT.json', 'd97ac2a9669ce2b4fe5ecb84e69cc2b2941ae2e35d1c099366dbcb80e77c7f79')
for rel,h in root['raw_logs_sha256'].items():
    bound(runtime/rel, h)
check(root['nonroot_uids'] == [1001,1001] and root['default_kernel_and_comparator'] == 'PASS', 'actual nonroot kernel/Comparator audit')
check(root['all_rejection_regression_sandbox_controls'] == 'PASS', 'actual required controls audit')
identity = load(runtime/'RUNTIME-IDENTITY.json')
for rel,h in identity['raw_API_hashes'].items():
    original = load(RUN/rel,h)
    if rel == 'run.json':
        check(all(original[k] == v for k,v in identity['run'].items()), 'privacy-preserving actual run projection')
    elif rel == 'jobs.json':
        jobs = {j['id']: j for j in original['jobs']}
        for row in identity['jobs']:
            check(all(jobs[row['id']][k] == v for k,v in row.items()), 'privacy-preserving actual job projection '+str(row['id']))

runtime_review = B/'reviews/MF07-ie13-canonical-35172783207'
rm = load(runtime_review/'MANIFEST.json', 'c0a6142a37fbc3cf4eda420736b543b88b4950d6656e76b0d7c9633672327942')
for rel,h in rm['files'].items():
    original = bound(runtime_review/rel,h)
    check(candidate['reviews/canonical-runtime/'+rel] == original, 'unaltered independent runtime report '+rel)
for path,h in load(runtime_review/'SOURCE-BINDINGS.json').items():
    # Retained referee map is an original-scope record, not relocated evidence.
    if isinstance(h,str) and len(h)==64:
        src=Path(path)
        if src.is_relative_to(W):
            rel=str(src.relative_to(W))
            check(sha(git(rel)) == h, 'referee literal original '+rel)
        else:
            bound(src,h)

cp = (runtime/'comparator.log').read_text()
names = config['theorem_names']
seen = re.findall(r"info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^]]+)\]", cp)
check([name for name,_ in seen] == names, 'all18 actual Solution axiom reports ordered')
check(all(set(x.strip() for x in axioms.split(',')) == {'propext','Classical.choice','Quot.sound'} for _,axioms in seen), 'all18 measured standard axiom sets')
check('Lean default kernel accepts the solution\nYour solution is okay!' in cp and cp.rstrip().endswith('EXIT_STATUS=0'), 'actual final kernel and Comparator success')
check("Illegal axiom detected: 'sorryAx'" in (runtime/'negative-sorry.log').read_text(), 'actual sorry rejection')
check('native_decide.ax_' in (runtime/'negative-native.log').read_text(), 'actual native rejection')
check('PASS: all three actual Comparator.runBuiltinKernel cases behaved as required' in (runtime/'kernel-controls.log').read_text(), 'all3 actual kernel controls')
check('PASS: all five Comparator regressions' in (runtime/'comparator-controls.log').read_text(), 'all5 actual Comparator regressions')
check((runtime/'sandbox.log').read_text().count('Sandbox UID: 1001') == 2, 'both actual sandbox modes nonroot')

before = (P/'before'/CANON).read_bytes()
after = (P/'overlay'/CANON).read_bytes()
suffix = before[before.index(b'<!-- colbrook-jsr-growth -->'):]
check(after[after.index(b'<!-- colbrook-jsr-growth -->'):] == suffix, 'full existing mathematics/target/history suffix unchanged')
check(sha(before.split(b'## Context and notation\n',1)[1]) == t['original_target_suffix_sha256'], 'original target suffix identity')
old = (P/'before/RESOLVED.md').read_text(); new = (P/'overlay/RESOLVED.md').read_text()
check(old.split('**MF-07 — affirmative resolution.**')[0] == new.split('**MF-07 — affirmative resolution;')[0], 'RESOLVED prefix unchanged')
check(old.split('**MF-12 —')[1:] == new.split('**MF-12 —')[1:], 'RESOLVED following entries unchanged')
original = load(P/'overlay'/PROJECT/'verification/publication/ORIGINAL-MATHEMATICS.json')
check(sha(git(original['path'])) == original['sha256'], 'original shared Colbrook manuscript literal identity')

# Complete schema/coverage validator on a temporary, source-identical private
# project. No Lean invocation, no writes into the coordinator's worktree.
temp = R/'schema-project'
check(not temp.exists(), 'fresh private static-validation copy')
for rel,data in candidate.items():
    dest=temp/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
validator_data = git('tools/lean/validate_manifest.py')
schema_data = git('docs/lean/schema/v0.4.schema.json')
(R/'validate_manifest.py.txt').write_bytes(validator_data)
(R/'v0.4.schema.json').write_bytes(schema_data)
space={'__name__':'publication_review_validator','__file__':str(W/'tools/lean/validate_manifest.py')}
exec(compile(validator_data, 'literal-proof-commit/validate_manifest.py', 'exec'),space)
capture=io.StringIO()
from contextlib import redirect_stdout
with redirect_stdout(capture):
    space['validate'](temp,json.loads(schema_data))
(R/'schema-validation.log').write_text(capture.getvalue())
check('PASS (18 declarations)' in capture.getvalue(), 'actual unchanged completed-project schema/coverage validator')
import yaml
meta=yaml.safe_load(candidate['formalization.yaml'])
for item in meta['status']['main_results']:
    check(sha(candidate[item['file']]) == item['file_sha256'], 'advertised source hash '+item['declaration'])
    check(item['declaration'].split('.')[-1] in candidate[item['file']].decode().splitlines()[item['line']-1], 'advertised source line '+item['declaration'])
check(meta['verification']['canonical_run']['proof_commit']==REV, 'metadata names actual proof commit')
check(meta['status']['whole_problem_verified'] is True, 'metadata proof status matches accepted original target')
check('pending' in meta['verification']['publication'], 'metadata explicitly pending publication execution')
shutil.rmtree(temp)

all_paths=set(subprocess.check_output(['git','-C',str(W),'ls-tree','-r','--name-only',REV],text=True).splitlines())|set(t['overlay'])
for rel in [CANON, PROJECT+'/README.md', PROJECT+'/verification/linux-35172783207/README.md']:
    content=(P/'overlay'/rel).read_text()
    for link in re.findall(r'\]\(([^)]+)\)',content):
        link=link.split('#',1)[0]
        if not link or '://' in link:
            continue
        target=os.path.normpath(str(PurePosixPath(rel).parent/link))
        check(target in all_paths, 'active local link '+rel+' -> '+target)
template=git('.github/PULL_REQUEST_TEMPLATE.md').decode()
pr=(P/'PR-BODY.md').read_text()
check(re.findall(r'^## .+$',pr,re.M)==re.findall(r'^## .+$',template,re.M), 'actual upstream PR template headings')
check('Replace this paragraph with the measured results before posting' in pr, 'draft PR body cannot misclaim later publication checks')
email=re.compile(rb'[A-Za-z0-9.!#$%&\x27*+/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+')
for rel in t['overlay']:
    check(not email.search((P/'overlay'/rel).read_bytes()), 'no contact string in overlay '+rel)
check(not email.search(pr.encode()), 'no contact string in draft PR body')
write('SOURCE-CONTINUATION.json', {'literal_proof_commit':REV,'proof_sources':t['protected_math_files'],
      'original_input_count':len(base),'proposed_project_inputs':{k:sha(v) for k,v in sorted(candidate.items())},
      'modified_existing_project_inputs':modified,'no_Lean_or_Git_mutation':True})
write('BINDINGS.json',bindings)
write('CHECKS.json', {'reviewer':'/root/mi04_independent_referee','role':'Nonauthor MF07 proof and publication reviewer',
      'checks':checks,'check_count':len(checks),'binding_count':len(bindings),'verdict':'APPROVE private publication overlay with stated later gates',
      'original_inputs':len(base),'prospective_project_inputs':len(candidate),'proof_sources':21,'exports':18,
      'local_Lean_execution':False,'PDF_render_or_visual_review':False,'Git_or_publication_mutation':False,'count_change':0})
print(json.dumps({'passed_checks':len(checks),'bindings':len(bindings),'project_inputs':len(candidate),'compiler_run':False}))
