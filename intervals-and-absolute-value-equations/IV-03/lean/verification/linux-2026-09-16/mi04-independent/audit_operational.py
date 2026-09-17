"""Authenticate exact IV03 canonical execution and source bytes; never invoke Lean."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import zipfile

P = Path(__file__).resolve().parent
R = P.parent
B = Path('/tmp/nla-lean-next-20260915')
G = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
PROJECT = 'intervals-and-absolute-value-equations/IV-03/lean'
PUBLISHED = 'cef3e2f486285d0f6885231cda3ac2ff04c975cb'
assert not (P / 'OPERATIONAL-CHECKS.json').exists(), 'Do not overwrite a completed audit'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def obj(p):
    return json.loads(p.read_text())

def git(*args):
    return subprocess.check_output(['git','-c','gc.auto=0',*args],cwd=G)

def put(name,value):
    (P / name).write_text(json.dumps(value,indent=2,sort_keys=True) + '\n')

meta = obj(R / 'run.json')
assert meta['repository']['full_name'] == 'sgstepaniants/OpenProblemsInNLA'
assert meta['id'] == 35059255598 and meta['head_sha'] == PUBLISHED
assert meta['event'] == 'push' and meta['status'] == 'completed' and meta['conclusion'] == 'success'
receipts = list((R / 'artifacts/lean-IV-03').glob('verify-*/result.json'))
assert len(receipts) == 1
receipt_path = receipts[0]
receipt = obj(receipt_path)
actual = receipt['repository_commit']
assert actual == PUBLISHED
assert receipt['project'] == PROJECT and receipt['result'] == 'comparator-accepted'
audit = obj(R / 'ROOT-AUDIT.json')
assert audit['actual_checkout'] == actual and audit['api_head'] == PUBLISHED
assert audit['bound_inputs'] == 140 and len(audit['exports']) == 4
assert audit['default_kernel_and_comparator'] == 'PASS'
assert audit['all_rejection_regression_sandbox_controls'] == 'PASS'
assert audit['literal_published_commit'] is True
candidate_path = B / 'IV03-CAMPAIGN-CANDIDATE.json'
assert sha(candidate_path.read_bytes()) == '432fcd10b90f5bced2c4d6c154ff7e903c02062311678f5075e2b4737417daa9'
candidate = obj(candidate_path)
import_bindings = obj(B / 'reviews/IV03-import-independent/ALL-140-PACKAGE-INPUTS.json')
assert candidate['files'] == import_bindings == receipt['input_sha256']

blobs = {}
for entry in git('ls-tree','-r','-z',actual,'--',PROJECT).split(b'\0'):
    if not entry:
        continue
    desc,path = entry.split(b'\t',1)
    mode,kind,blob = desc.split()
    assert kind == b'blob' and mode in [b'100644',b'100755']
    rel = path.decode()[len(PROJECT)+1:]
    assert '.lake' not in Path(rel).parts and Path(rel).suffix not in ['.olean','.ilean','.so','.a','.o']
    blobs[rel] = blob.decode()
assert set(blobs) == set(receipt['input_sha256']) and len(blobs) == 140
bindings = []
for rel,blob in sorted(blobs.items()):
    raw = git('cat-file','blob',blob)
    assert sha(raw) == receipt['input_sha256'][rel]
    bindings.append({'path':rel,'actual_git_blob':blob,'sha256':sha(raw),
                     'receipt_and_independently_approved_package_match':True})
put('ALL-140-INPUT-BINDINGS.json',bindings)

prior = B / 'reviews/IV03-mi04-independent'
active = obj(prior / 'ALL-14-SOURCE-BINDINGS.json')
assert len(active) == 14
maths = {}
for rel,row in active.items():
    raw = git('show',actual + ':' + PROJECT + '/' + rel)
    assert sha(raw) == row['sha256']
    assert raw == (prior / 'reviewed-source' / (rel + '.txt')).read_bytes()
    maths[rel] = {'sha256':sha(raw),'unchanged_from_original_published_and_two_referees':True}
put('ALL-14-ACTIVE-SOURCE-BINDINGS.json',maths)
freeze = json.loads(git('show',actual + ':' + PROJECT + '/statement-freeze.json'))
assert len(freeze['sha256']) == 7
for rel,h in {**freeze['sha256'],**freeze['reports']}.items():
    assert sha(git('show',actual + ':' + PROJECT + '/' + rel)) == h
put('FROZEN-7-AND-STATEMENT-REVIEW-BINDINGS.json',freeze)
config = receipt['config']
assert len(config['theorem_names']) == 4 and config['definition_names'] == []
assert config['permitted_axioms'] == ['propext','Classical.choice','Quot.sound']
solution = git('show',actual + ':' + PROJECT + '/Solution.lean').decode()
assert solution.count('#assert_trust kernel ') == 4

jobs = obj(R / 'jobs.json')['jobs']
job = next(j for j in jobs if j['name'] == 'verify (IV-03, ' + PROJECT + ')')
assert job['conclusion'] == 'success'
raw_path = R / f"job-{job['id']}.log"
raw = raw_path.read_text(encoding='utf-8-sig')
assert re.search(r'git log -1 --format=%H\n[^\n]*' + re.escape(actual) + r'\n',raw)
raw_lines = [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?','',line) for line in raw.splitlines()]
logs = []
for log in sorted(receipt_path.parent.glob('*.log')):
    lines = log.read_text().splitlines()
    payload = [line for line in lines if line and not line.startswith('$ ') and not line.startswith('EXIT_STATUS=')]
    pos = 0
    for line in payload:
        while pos < len(raw_lines) and raw_lines[pos] != line:
            pos += 1
        assert pos < len(raw_lines),(log.name,line)
        pos += 1
    logs.append({'path':str(log.relative_to(R)),'sha256':sha(log.read_bytes()),
                 'lines':len(lines),'payload_lines':len(payload),
                 'all_payload_lines_match_authenticated_raw_job_in_order':True})
assert len(logs) == 9
comp = (receipt_path.parent / 'comparator.log').read_text()
for rel in active:
    assert 'Built ' + rel[:-5].replace('/','.') + ' ' in comp,rel
for name in config['theorem_names']:
    assert "'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]" in comp,name
sandbox = (receipt_path.parent / 'sandbox.log').read_text()
for marker in ['NEGATIVE unknown option: exit=2','NEGATIVE unexpected --rw: exit=2',
               'NEGATIVE unexpected --rwx: exit=2','NEGATIVE relative --rwx: exit=2',
               'PASS nested namespace write attempt: rejected','PASS outside .lake write-open: denied',
               'PASS host loopback listener: unreachable']:
    assert marker in sandbox,marker
controls_job = next(j for j in jobs if j['name'] == 'checker-controls')
assert controls_job['conclusion'] == 'skipped'
artifact = next(a for a in obj(R / 'artifacts.json')['artifacts'] if a['name'] == 'lean-IV-03')
archive = R / 'lean-IV-03.zip'
assert artifact['digest'] == 'sha256:' + sha(archive.read_bytes())
assert artifact['workflow_run']['head_sha'] == PUBLISHED and artifact['workflow_run']['id'] == meta['id']
with zipfile.ZipFile(archive) as z:
    members = [name for name in z.namelist() if not name.endswith('/')]
    for name in members:
        assert z.read(name) == (R / 'artifacts/lean-IV-03' / name).read_bytes(),name
for rel in ['tools/lean','docs/lean/schema','.github/workflows/lean-verification.yml']:
    assert git('diff','ba0de2339ed9d8226a1fda69b6824f4972eca549',actual,'--',rel) == b''

report = {'reviewer':'/root/mi04_independent_referee; independent AI operational reviewer',
 'audited_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'ACCEPT actual fresh canonical Linux execution on the literal candidate commit',
 'run':meta['id'],'job':job['id'],'repository':meta['repository']['full_name'],
 'api_head':PUBLISHED,'actual_receipt_checkout':actual,'literal_candidate_checkout':True,
 'all140_project_inputs_match_Git_receipt_and_independently_approved_import':True,
 'all14_active_sources_match_original_published_source_and_both_complete_reviews':True,
 'all7_frozen_inputs_and_two_statement_reviews_unchanged':True,
 'all4_exports_and_LeanCert_kernel_trust_accepted':True,
 'default_kernel_and_Comparator':'PASS in actual fresh run',
 'required_controls':'PASS: three actual kernel cases, five Comparator regressions, sorry/native rejection, actual build/export isolation and four malformed-option cases',
 'separate_controls_job':'skipped; all required per-project controls ran in the successful proof job',
 'all9_log_payloads_match_raw_job_in_order':logs,
 'artifact_id':artifact['id'],'artifact_sha256':sha(archive.read_bytes()),
 'receipt_sha256':sha(receipt_path.read_bytes()),
 'shared_runtime_audit_sha256':sha((R / 'ROOT-AUDIT.json').read_bytes()),
 'shared_script_label_disclosure':'The shared audit has fixed reviewer label /root. This child referee actually executed it; that field does not claim another root manual review.',
 'local_Lean_or_Lake':False,'proof_or_branch_edits':False,'PR_or_count_changes':False,
 'scope':'Authentication of a real separate Linux proof execution and exact source binding; mathematical review is supplied separately. GitHub, runner, pinned tools and checker remain trust dependencies.'}
put('OPERATIONAL-CHECKS.json',report)
print(json.dumps({'verdict':report['verdict'],'checkout':actual,'inputs':140,'active_sources':14,
                  'exports':4,'artifact':artifact['id'],'CHECKS_sha256':sha((P / 'OPERATIONAL-CHECKS.json').read_bytes())},indent=2))
