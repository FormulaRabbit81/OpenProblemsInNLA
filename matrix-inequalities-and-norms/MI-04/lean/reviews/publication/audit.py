from pathlib import Path
import json, hashlib, subprocess, re, zipfile, datetime, collections, yaml
B=Path('/tmp/nla-lean-next-20260915'); W=Path('/private/tmp/nla-lean-next-mi04-worktree'); R=B/'reviews/MI04-ie13-publication-63340'
P=W/'matrix-inequalities-and-norms/MI-04/lean'; H='63340ef17139606dce03c4d9000288129b773157'; prior=B/'reviews/MI04-ie13-canonical-runtime-35150473054'
sha=lambda b:hashlib.sha256(b).hexdigest()
def digest(p):return sha(Path(p).read_bytes())
def obj(p):return json.loads(Path(p).read_text())
def dump(name,x):(R/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.check_output(['git','-C',str(W),*args])
def blob(rel):return git('show',H+':'+rel)
bindings={}
def bind(p):bindings[str(Path(p).resolve())]=digest(p);return digest(p)
assert git('rev-parse','HEAD').decode().strip()==H
assert not git('diff','--cached','--name-only').strip()
changed=set(git('diff','--name-only','-z').decode().split('\0'))-{''}; new=set(git('ls-files','--others','--exclude-standard','-z').decode().split('\0'))-{''}
assert len(changed)==13 and len(new)==37
paths=sorted(changed|new); pubmap={rel:bind(W/rel) for rel in paths}
assert len(paths)==50
math=obj(P/'verification/publication/ACCEPTED-TRANSITION.json')['all21_math_files_unchanged'];assert len(math)==21
for rel,h in math.items():
 assert bind(P/rel)==h and (P/rel).read_bytes()==blob('matrix-inequalities-and-norms/MI-04/lean/'+rel)
old=obj(prior/'GIT-INPUTS.json');assert old['commit']==H and len(old['sha256'])==233
changed_old=[]
for rel,h in old['sha256'].items():
 if digest(P/rel)!=h:changed_old.append(rel)
assert sorted(changed_old)==['PUBLICATION-EVIDENCE.json','README.md','formalization.yaml']
for rel,mark in [('README.md','## Problem statement'),('problem.tex','\\subsection{Problem statement}'),('solution.tex','% BEGIN REVIEWED PROOF')]:
 path='matrix-inequalities-and-norms/MI-04/'+rel; before=blob(path).decode();after=(W/path).read_text()
 assert before[before.index(mark):]==after[after.index(mark):]
# Frozen originals and current active bytes stay exactly as in the accepted proof revision.
frozen=obj(P/'STATEMENT-FREEZE.json')['frozen_files_sha256']
for rel,h in frozen.items():
 snap=P/'statement-audit/snapshots'/rel;assert bind(snap)==h
 assert (P/rel).read_bytes()==blob('matrix-inequalities-and-norms/MI-04/lean/'+rel)
for rel in ['problem_ids.json','tools/update_catalog.py','tools/validate_problem_ids.py','tools/lean/validate_manifest.py','tools/lean/verify.sh','tools/lean/harness.py','tools/lean/source-lock.json','docs/lean/schema/v0.4.schema.json']:
 assert (W/rel).read_bytes()==blob(rel);bind(W/rel)
for p in (W/'.github/workflows').glob('*'):
 if p.is_file():assert p.read_bytes()==blob(str(p.relative_to(W)));bind(p)
# Full public execution payload and the previous independent review are exact copies.
public=P/'verification/linux-2026-09-16';original=B/'MI04-canonical-run-35150473054';runtime_exact=[]
for p in public.rglob('*'):
 if p.is_file() and p.name not in ['README.md','source-lock.json']:
  q=original/p.relative_to(public);assert p.read_bytes()==q.read_bytes();bind(q);runtime_exact.append(str(p.relative_to(public)))
assert len(runtime_exact)==22
assert (public/'source-lock.json').read_bytes()==blob('tools/lean/source-lock.json')
for name in ['CHECKS.json','GIT-INPUTS.json','MANIFEST.json','REVIEW.md','SOURCE-BINDINGS.json','audit.py']:
 assert (P/'reviews/canonical-runtime'/name).read_bytes()==(prior/name).read_bytes();bind(prior/name)
# Every promoted schema export still refers to its actual unchanged declaration/hash/line.
y=yaml.safe_load((P/'formalization.yaml').read_text()); conf=obj(P/'comparator.json'); names=conf['theorem_names']
results=y['status']['main_results'];assert len(results)==21 and set(names)=={x['declaration'] for x in results}
for x in results:
 src=P/x['file'];assert digest(src)==x['file_sha256'];line=src.read_text().splitlines()[x['line']-1]
 assert re.search(r'\b(?:lemma|theorem)\s+'+re.escape(x['declaration'].split('.')[-1])+r'\b',line)
 assert set(x['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert y['status']['whole_problem_verified'] is True
assert not any('actual full acceptance pending' in str(x) for x in y['related_formalizations'])
assert y['verification']['candidate_canonical_run']['literal_proof_commit']==H
assert y['verification']['candidate_canonical_run']['run_id']==35150473054
# Scan added/changed text and every new ZIP member; no contact values are emitted.
pattern=re.compile(rb'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}');text_checked=0;zip_members=0
for rel in paths:
 p=W/rel
 if p.suffix=='.zip':
  with zipfile.ZipFile(p) as z:
   for name in z.namelist(): assert not pattern.search(z.read(name)),(rel,name);zip_members+=1
 elif p.suffix!='.pdf':assert not pattern.search(p.read_bytes()),rel;text_checked+=1
# Independent exact catalogue recount against literal immutable canonical pages.
registry=obj(W/'problem_ids.json');oldcounts=collections.Counter();newcounts=collections.Counter();changes=[]
q=subprocess.Popen(['git','-C',str(W),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for ident,rel in registry.items():
 q.stdin.write((H+':'+rel+'\n').encode());q.stdin.flush();n=int(q.stdout.readline().split()[2]);oldbytes=q.stdout.read(n);assert q.stdout.read(1)==b'\n'
 current=(W/rel).read_bytes() if (W/rel).exists() else oldbytes
 oldstatus=re.search(rb'\*\*Status:\*\*\s*(.+)',oldbytes).group(1).decode().strip();newstatus=re.search(rb'\*\*Status:\*\*\s*(.+)',current).group(1).decode().strip()
 oldcounts[oldstatus]+=1;newcounts[newstatus]+=1
 if oldstatus!=newstatus:changes.append([ident,oldstatus,newstatus])
q.stdin.close();assert q.wait()==0
assert changes==[['MI-04','Solved','Lean verified']]
assert dict(oldcounts)=={'Solved':64,'Open':42,'Partially resolved':71,'Lean verified':40}
assert dict(newcounts)=={'Solved':63,'Open':42,'Partially resolved':71,'Lean verified':41}
assert all('63 solved (published or independently audited); 41 solved with Lean verification.' in (W/rel).read_text() for rel in ['README.md','CATALOG.md'])
qa=B/'MI04-publication-pdf-qa';assert (W/'matrix-inequalities-and-norms/MI-04/solution.pdf').read_bytes()==(qa/'solution.pdf').read_bytes()
for name in ['solution.pdf','solution.tex','solution-pass1.log.txt','solution-pass2.log.txt']:
 bind(qa/name)
for name in ['solution-pass1.log.txt','solution-pass2.log.txt']:
 txt=(qa/name).read_text();assert not re.search(r'^!',txt,re.M) and 'Overfull' not in txt and '(4 pages)' in txt
# Record actual metadata validation invocation; no Lean process and no bytecode writes.
cmd=['/tmp/nla-lean-formalization/venv/bin/python',str(W/'tools/lean/validate_manifest.py'),str(P)]
import os
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
v=subprocess.run(cmd,env=env,capture_output=True,text=True);assert v.returncode==0
check=subprocess.run(['git','-C',str(W),'-c','core.whitespace=-blank-at-eol','diff','--check'],capture_output=True,text=True);assert check.returncode==0
assert git('rev-parse','HEAD').decode().strip()==H
assert pubmap=={rel:digest(W/rel) for rel in paths}
dump('PUBLICATION-SOURCE-MAP.json',pubmap)
dump('CHECKS.json',{'reviewer':'/root/ie13_continuation','scope':'Independent nonauthor documentation/status publication review; no new Lean run','base_commit':H,'changed_tracked_files':13,'new_files':37,'unchanged_math_files':21,'unchanged_prior_project_inputs':230,'changed_prior_inputs':changed_old,'unchanged_frozen_originals':len(frozen),'runtime_byte_exact_files':22,'checker_source_lock_literal_git_exact':True,'runtime_review_byte_exact_files':6,'metadata_exports_exact':21,'text_contact_scan_files':text_checked,'zip_contact_scan_members':zip_members,'canonical_status_counts_before':dict(oldcounts),'canonical_status_counts_after':dict(newcounts),'only_status_change':changes,'all217_ids_paths_unchanged':True,'reviewed_target_and_mathematical_proof_suffixes_unchanged':True,'stale_related_note_corrected':True,'metadata_validation':{'argv':cmd,'exit_code':v.returncode,'stdout':v.stdout,'stderr':v.stderr},'default_python_attempt':'Stopped at missing jsonschema; rerun successfully with the already existing validation venv, no installation.','whitespace_check':'Passed with intentional Markdown hard-break trailing spaces allowed; default check reports that existing-style two-space break on the changed Status line.','pdf_qa':'Root reported independent visual inspection of three problem and four solution pages. Reviewer binds matching solution PDF/source and both successful four-page render logs, but claims no separate visual rendering.','later_merge_publication_PR_checks':'Not performed or assumed by this review.','Lean_Lake_Comparator_run_by_reviewer':False,'Git_worktree_mutation_by_reviewer':False,'campaign_count_change':0})
bind(Path(__file__));dump('SOURCE-BINDINGS.json',bindings)
print(json.dumps({'PASS':True,'publication_files':len(paths),'support_bindings':len(bindings),'source_map_sha256':digest(R/'PUBLICATION-SOURCE-MAP.json'),'checks_sha256':digest(R/'CHECKS.json')},indent=2))
