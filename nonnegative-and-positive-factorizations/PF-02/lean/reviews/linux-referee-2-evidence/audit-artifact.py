#!/usr/bin/env python3
"""Independent PF-02 artifact/source/provenance checks; never executes proof code."""
from pathlib import Path
import hashlib, json, re, subprocess, zipfile

e = Path(__file__).resolve().parent
p = e.parent.parent
root = p.parents[2]
a = p / 'verification/linux-2026-09-15'
runid, jobid, artifactid = 35021020857, 104556550871, 10418540042
commit = 'a3e984ced348f4d8529c5d0f8f87c9be7dd979e2'
v = a / 'verify-20260915T204142Z-4353'
sha = lambda b: hashlib.sha256(b).hexdigest()
filehash = lambda path: sha(path.read_bytes())
j = lambda path: json.loads(path.read_text())

api, jobs, run = (j(e / f) for f in ('artifact-api.json','jobs-api.json','run-api.json'))
assert api['id'] == artifactid and api['name'] == 'lean-PF-02'
assert api['workflow_run']['id'] == runid and api['workflow_run']['head_sha'] == commit
assert api['digest'] == 'sha256:' + filehash(a/'lean-PF-02.zip')
assert api['size_in_bytes'] == (a/'lean-PF-02.zip').stat().st_size == 17553
assert not api['expired']
assert run['id'] == runid and run['head_sha'] == commit and run['run_attempt'] == 1
assert run['status'] == 'completed' and run['conclusion'] == 'success'
assert run['repository']['full_name'] == 'ajt60gaibb/OpenProblemsInNLA'
assert run['head_branch'] == 'codex/lean-pf02' and run['path'] == '.github/workflows/lean-verification.yml'
job = next(x for x in jobs['jobs'] if x['id'] == jobid)
assert job['run_id'] == runid and job['head_sha'] == commit and job['run_attempt'] == 1
assert job['conclusion'] == 'success' and all(s['conclusion'] == 'success' for s in job['steps'])
assert 'ubuntu-24.04' in job['labels']
assert any(s['name'] == 'Fresh sandboxed statement, axiom and kernel verification' for s in job['steps'])
assert next(x for x in jobs['jobs'] if x['name']=='select')['conclusion'] == 'success'
assert next(x for x in jobs['jobs'] if x['name']=='checker-controls')['conclusion'] == 'skipped'
assert j(a/'artifact-provenance.json') == api
assert j(a/'job-provenance.json') == jobs
assert j(a/'run-provenance.json') == run

archived = {}
for line in (a/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ',1)
    assert filehash(a/name) == digest, name
    archived[name] = digest
assert len(archived) == 17
assert set(archived) == {str(f.relative_to(a)) for f in a.rglob('*') if f.is_file() and f.name != 'SHA256SUMS'}
with zipfile.ZipFile(a/'lean-PF-02.zip') as z:
    members = z.namelist()
    assert len(members) == len(set(members)) == 13
    for name in members:
        assert z.read(name) == (a/name).read_bytes(), name
assert sum(name.endswith('.log') for name in members) == 12

receipt = j(v/'result.json')
assert receipt['repository_commit'] == commit and receipt['project'] == str(p.relative_to(root))
assert receipt['result'] == 'comparator-accepted'
assert receipt['semantic_review'] == 'not-performed-by-this-command'
assert receipt['config'] == j(p/'comparator.json')
assert len(receipt['input_sha256']) == 70
tracked = subprocess.check_output(['git','ls-tree','-r','--name-only',commit,'--',str(p.relative_to(root))],cwd=root,text=True).splitlines()
assert set(receipt['input_sha256']) == {str(Path(n).relative_to(p.relative_to(root))) for n in tracked}
for name, digest in receipt['input_sha256'].items():
    assert filehash(p/name) == digest, name
    content = subprocess.check_output(['git','show',commit+':'+str((p/name).relative_to(root))],cwd=root)
    assert sha(content) == digest, name
for name, count in [('final-source-inputs.json',20),('statement-inputs.json',10)]:
    seal = j(p/'reviews'/name)['input_sha256']
    assert len(seal) == count
    assert all(receipt['input_sha256'][k] == val for k,val in seal.items())
freeze = j(p/'reviews/statement-freeze.json')
for name, digest in freeze['independent_statement_reports'].items():
    assert receipt['input_sha256'][name] == digest
source = j(p/'reviews/initial/source-hashes.json')
source_files = source.get('files', source.get('source_sha256', {}))
assert source_files
for name,digest in source_files.items():
    assert filehash(root/name) == digest

config = receipt['config']
names = config['theorem_names']
assert len(names) == 9 and config['definition_names'] == []
allowed = {'propext','Classical.choice','Quot.sound'}
assert set(config['permitted_axioms']) == allowed
clog = (v/'comparator.log').read_text()
assert clog.rstrip().endswith('EXIT_STATUS=0')
assert clog.count('declaration uses `sorry`') == 9
assert 'declaration uses `sorry`' not in clog.split('Building Solution',1)[1]
assert 'Running Lean default kernel on solution.\nLean default kernel accepts the solution\nYour solution is okay!' in clog
for module in ('Challenge','Solution'):
    line = next(x for x in clog.splitlines() if x.startswith('Exporting #[') and x.endswith(' from '+module))
    actual = re.findall(r'NLA\.PF02\.\w+',line)
    assert actual == names
closures = dict(re.findall(r"'(NLA\.PF02\.[^']+)' depends on axioms: \[([^\]]+)\]",clog))
assert len(closures) == 22
assert all(set(axes.split(', ')) == allowed for axes in closures.values())
assert all(name in closures for name in names)
assert 'interval_decide (trust := kernel)' in (p/'NLA/PF02/Data.lean').read_text()
assert (p/'NLA/PF02/Topology.lean').read_text().count('thirty_two_pos') == 2

for log in a.rglob('*.log'):
    expected = 1 if log.name in ('negative-sorry.log','negative-native.log') else 0
    assert log.read_text().rstrip().endswith('EXIT_STATUS='+str(expected)),log
kernel = (v/'kernel-controls.log').read_text()
for token in ['RETURN honest_with_inductives_and_quotients: accepted',
              "RETURN invalid_raw_proof: rejected: while replaying declaration 'PinnedReplayProbe.invalid'",
              'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift',
              'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    assert token in kernel
cctrl = (v/'comparator-controls.log').read_text()
for label in ['simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch','type_mismatch']:
    assert 'PASS '+label+':' in cctrl
assert "Illegal axiom detected: 'sorryAx'" in (v/'negative-sorry.log').read_text()
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in (v/'negative-native.log').read_text()
sandbox=(v/'sandbox.log').read_text()
for token in ['MODE build: exit=0','MODE export: exit=0','Sandbox UID: 1001',
              'PASS effective capabilities: none','PASS no_new_privs: set',
              'PASS AF_UNIX socket creation: denied','PASS host loopback listener: unreachable',
              'PASS nested namespace write attempt: rejected exit=1',
              'Outer and export fixture contents unchanged; only designated build fixture written.']:
    assert token in sandbox
for namespace in ['user','pid','mnt','net','ipc','uts']:
    assert sandbox.count('PASS '+namespace+' namespace: private') == 2
for label in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:
    assert 'NEGATIVE '+label+': exit=2' in sandbox

lock=j(root/'tools/lean/source-lock.json')
for source_path in ['tools/lean/source-lock.json','tools/lean/harness.py','.github/workflows/lean-verification.yml']:
    assert sha(subprocess.check_output(['git','show',commit+':'+source_path],cwd=root)) == filehash(root/source_path)
assert receipt['source_lock_sha256'] == filehash(root/'tools/lean/source-lock.json')
t=receipt['tool_receipt']
assert t['source_lock_sha256'] == receipt['source_lock_sha256']
assert t['forsythe_commit'] == lock['commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert t['lean_toolchain'] == lock['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert t['ci_sandbox_probe_sha256'] == '31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803'
assert set(t['executables']) == {'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'}
assert t['go_version'] == 'go version go1.27.1 linux/amd64'
dep=(v/'dependencies.log').read_text()
for package in j(p/'lake-manifest.json')['packages']:
    assert "checking out revision '"+package['rev']+"'" in dep

record={
 'reviewer':'OpenAI Codex GPT-6 AI agent /root/existing_verification_audit; independent non-implementing referee',
 'phase':'independent audit of actual authenticated Linux artifact',
 'mechanical_checks':'PASS',
 'run_id':runid,'job_id':jobid,'artifact_id':artifactid,'run_attempt':1,'proof_commit':commit,
 'artifact_sha256':filehash(a/'lean-PF-02.zip'),'receipt_sha256':filehash(v/'result.json'),
 'comparator_log_sha256':filehash(v/'comparator.log'),
 'archive_member_count':13,'logs_read':12,'archive_sha256_manifest_files':17,
 'receipt_input_count':70,'all_receipt_inputs_match_current_and_git':True,
 'receipt_includes_entire_tracked_project_at_proof_commit':True,
 'all_final20_and_frozen10_inputs_match':True,'source_hashes':source_files,
 'actual_exported_theorems':names,'actual_printed_axiom_closures':{n:a.split(', ') for n,a in closures.items()},
 'permitted_axioms':sorted(allowed),'default_kernel_acceptance':True,
 'raw_kernel_controls':3,'comparator_regression_cases':5,'sorry_and_native_rejected':True,
 'sandbox_build_and_export_checks_passed':True,'standalone_checker_controls_job':'skipped; all mandatory controls executed inside verify',
 'tool_receipt':t,
 'shared_source_hashes':{n:filehash(root/n) for n in ['tools/lean/source-lock.json','tools/lean/harness.py','.github/workflows/lean-verification.yml']},
 'archive_sha256':archived,
 'independent_api_sha256':{name:filehash(e/name) for name in ['artifact-api.json','jobs-api.json','run-api.json']},
 'review_source_sha256':{name:filehash(p/'reviews'/name) for name in ['statement-referee-1.md','statement-referee-2.md','final-referee-1.md','final-referee-2.md']},
 'limitations':['Independent artifact audit, not a second newly executed Linux build.','Binary hashes are authenticated runner receipt values; reviewer did not rebuild Linux executables locally.','Pinned Mathlib cache is dependency reuse; source proof project rebuilt from committed inputs.','Operational checks alone do not establish natural-language correspondence; the two sealed source reviews supply that gate.']}
(e/'audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: GitHub digest/provenance, 13 ZIP members, 17 archived hashes, all 70 current/Git inputs, both seals, all 9 exported targets and 22 standard-axiom closures, all actual kernel/Comparator/sandbox controls.')
