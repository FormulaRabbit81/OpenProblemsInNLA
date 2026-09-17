"""Private RA02 packaging of already tested sources; no Lean, Git or network execution."""
from pathlib import Path
import datetime,difflib,hashlib,json,os,re,subprocess,sys
import jsonschema,yaml

B=Path('/tmp/nla-lean-next-20260915').resolve()
W=B/'next-proofs/RA-02'
L=Path('/private/tmp/nla-lean-local-shared-20260916')
I=Path('/private/tmp/nla-lean-next-mf22-worktree')
P=B/'RA02-canonical-package-local19'
H=B/'RA02-canonical-local19-handoff'
ACCEPTANCE=B/'RA02-LOCAL-DEVELOPMENT-ACCEPTANCE.json'
ACCEPTANCE_SHA='20065f375d68844883266d7ec86176b07ddcb652710c693dd67e3d2b1ff005f3'
ASSEMBLY=L/'ASSEMBLY-19.json'
WRAPPER='NLA/RA02/Complete.lean'
SCHEMA_SHA='25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
REVIEWS={
 'RA02-full-final-referee':'1007c48fffb31e939cd3de124e70a42ab13591346bb44a34d216fdc152677af1',
 'RA02-ie13-final-local-development19':'b333792c5421b355fbeb5427ee0d897ee3a2648c036278b78bf89d7b31b108ff'}
PERMITTED={'propext','Classical.choice','Quot.sound'}
EMAIL=re.compile(rb'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
checks=[];bindings={};retained=[];omitted=[]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
canon=lambda p:'Solution.lean' if p==WRAPPER else p

def check(q,s):
    if not q:raise ValueError(s)
    checks.append(s)
def bind(p,h=None):
    p=Path(p).resolve();v=sha(p)
    check(h is None or v==h,'hash '+str(p));bindings[str(p)]=v;return p
def put(rel,data):
    p=P/rel;check(not p.exists(),'new path '+rel)
    if isinstance(data,str):data=data.encode()
    check(EMAIL.search(data)is None,'no email '+rel)
    p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def dump(rel,value):put(rel,json.dumps(value,indent=2,ensure_ascii=False)+'\n')
def copy(src,rel):
    src=bind(src);put(rel,src.read_bytes());retained.append({'original_path':str(src),'path':rel,'sha256':sha(src)})
def reference(src,rel,url=None):
    src=bind(src)
    if EMAIL.search(src.read_bytes()):
        omitted.append({'original_path':str(src),'intended_path':rel,'sha256':sha(src),'immutable_source':url,'reason':'Contact-bearing historical reference remains private; no active proof omitted.'})
    else:copy(src,rel)
def gethash(value):return value['sha256'] if isinstance(value,dict) else value

check(not P.exists() and not H.exists(),'new private package and handoff only')
a=read(bind(ACCEPTANCE,ACCEPTANCE_SHA));assembly=read(bind(ASSEMBLY,a['assembly_sha256']))
check(a['reviewer']=='/root' and a['complete_development_graph_passed'],'actual coordinator complete local acceptance')
check(a['platform']=='darwin' and a['frozen_export_count']==27 and a['count_change']==0,'local-only exact27 acceptance')
check(not a['canonical_verification_completed'] and not a['comparator_run'],'canonical checks not yet run')
rows={k:v for k,v in assembly['sources'].items() if k.startswith('NLA/RA02/')}
check(len(rows)==35 and WRAPPER in rows,'all35 actual source inputs including Complete')
canonical={canon(k):v['sha256']for k,v in rows.items()}
check(canonical==a['accepted_source_sha256'],'all35 exact accepted source hashes')
for k,v in rows.items():
    bind(v['source'],v['sha256']);bind(a['selected_source_locations'][canon(k)],v['sha256'])
texts={canon(k):Path(v['source']).read_text()for k,v in rows.items()}
graph={k:[x.replace('.','/')+'.lean'for x in re.findall(r'(?m)^import\s+(\S+)',Path(v['source']).read_text())if x.startswith('NLA.')]for k,v in rows.items()}
seen=set();todo=[WRAPPER]
while todo:
    k=todo.pop()
    if k in seen:continue
    check(k in graph,'all transitive imports present '+k);seen.add(k);todo.extend(graph[k])
check(seen==set(rows),'final Solution import closure reaches all35 inputs')
check(all(not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*axiom\s',t,re.M)for t in texts.values()),'all active sources hole-free with no native trust or custom axioms')
check(all('import Challenge'not in t for t in texts.values()),'Challenge never imported')
cfg=read(bind(W/'comparator.json'));names=cfg['theorem_names']
check(len(names)==len(set(names))==27 and cfg['definition_names']==[] and set(cfg['permitted_axioms'])==PERMITTED,'exact27 immutable Comparator boundary')
check(set(a['observed_axioms'])==set(names) and all(set(v)==PERMITTED for v in a['observed_axioms'].values()),'all27 actual standard axiom lists')
wrapper=texts['Solution.lean']
check(re.findall(r'(?m)^import\s+(\S+)',wrapper)==['NLA.RA02.FinalCounterexample'],'unchanged export-only wrapper')
check(re.findall(r'(?m)^#assert_trust kernel (\S+)$',wrapper)==names,'all27 exact kernel assertions')
check(re.findall(r'(?m)^#print axioms (\S+)$',wrapper)==names,'all27 exact axiom output requests')
freeze=read(bind(W/'STATEMENT-FREEZE.json'));frozen=freeze['frozen_files']
check(len(frozen)==9 and frozen==a['frozen_files_sha256'],'exact frozen_files nine-file boundary')
for k,h in frozen.items():bind(W/k,h)
challenge=(W/'Challenge.lean').read_text();results=[];contract_map={}
for full in names:
    short=full.removeprefix('NLA.RA02.');pat=re.compile(r'(?m)^(?:theorem|lemma)\s+'+re.escape(short)+r'\b')
    found=[(k,m)for k,t in texts.items()for m in pat.finditer(t)]
    check(len(found)==1,'unique actual implementation '+full);k,m=found[0]
    expected=re.search(r'(?ms)^theorem\s+'+re.escape(short)+r'\b(.*?):= by',challenge)
    actual=re.search(r'(?ms)^(?:theorem|lemma)\s+'+re.escape(short)+r'\b(.*?):= by',texts[k])
    check(expected is not None and actual is not None,'read header '+full)
    check(' '.join(expected.group(1).split())==' '.join(actual.group(1).split()),'whitespace-normalized frozen header '+full)
    contract_map[full]={'file':k,'file_sha256':canonical[k],'header_matches_after_whitespace_only':True}
    results.append({'declaration':full,'file':k,'line':texts[k].count('\n',0,m.start())+1,'file_sha256':canonical[k],'sorry_count':0,'axioms':a['observed_axioms'][full],'comparator_config':'comparator.json','verification_status':'Actual local source compilation and kernel assertions passed; fresh non-root Linux replay, Comparator and controls pending.'})
check('interval_decide (trust := kernel)'in texts['NLA/RA02/Numerical.lean'] and 'rank_denominator_le_three r'in texts['NLA/RA02/ExponentialComparison.lean'],'consumed kernel LeanCert certificate retained')
check({p['name']:p['rev']for p in read(W/'lake-manifest.json')['packages']}==a['dependency_commits'],'all dependency pins exact')
receipt=read(bind(a['receipt'],a['receipt_sha256']))
check(receipt.get('end') and not receipt['failed_modules'] and not receipt['blocked_modules'],'actual terminal complete local19 receipt')
check(receipt['max_compiler_processes']==1 and receipt['threads']==1 and receipt['memory_cap_mib']==4096,'actual serial one-thread4096MiB final execution')
fresh=[x for x in receipt['commands'] if x.get('exit_code')==0]
reused=[x for x in receipt['commands'] if x.get('status')=='reused_exact_successful_local_output']
check(len(fresh)==3 and len(reused)==32 and len(receipt['commands'])==35,'three fresh plus32 authenticated reused outputs')
check({x['module']for x in fresh}=={'NLA.RA02.ExponentialComparison','NLA.RA02.FinalCounterexample','NLA.RA02.Complete'},'exact three fresh commands')
runtime_paths=set()
check(set(a['actual_commands'])=={k[:-5].replace('/','.')for k in rows},'origins for all35 sources')
for mod,c in a['actual_commands'].items():
    check(c['exit_code']==0 and c['source_sha256']==rows[mod.replace('.','/')+'.lean']['sha256'],'actual source-matched successful origin '+mod)
    rp=bind(c['receipt'],c['receipt_sha256']);lp=bind(c['log'],c['log_sha256']);runtime_paths.update([rp,lp])
    cr=read(rp);command=next(x for x in cr['commands'] if x['module']==mod)
    check(bool(cr.get('end')) and command.get('exit_code')==0 and command['source_sha256']==c['source_sha256'] and command['log_sha256']==c['log_sha256'],'literal original terminal command '+mod)
    check('error:'not in lp.read_text(),'successful origin log '+mod)
    check('--threads=1'in c['argv'] and any(x in c['argv']for x in ['--memory=3072','--memory=4096']),'one-thread bounded original compiler '+mod)
for p,h in a['bindings'].items():
    q=bind(p,h);check(q.is_relative_to(L) and q.suffix in {'.json','.log'},'bounded root acceptance binding '+p);runtime_paths.add(q)
actual_final=Path(a['actual_commands']['NLA.RA02.Complete']['log']).read_text()
actual_axioms={n:[s.strip()for s in raw.split(',')if s.strip()]for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",actual_final)}
check(actual_axioms==a['observed_axioms'],'measured final27 axiom lists exact')
root_audit=bind(B/'audit_ra02_local_development19.py',a['audit_script_sha256'])
review_manifests={}
for name,h in REVIEWS.items():
    q=B/'reviews'/name;manifest=read(bind(q/'MANIFEST.json',h));review_manifests[name]=manifest
    for fn,v in manifest['files'].items():bind(q/fn,gethash(v))
    sm=read(q/('SOURCE-MAP.json'if name=='RA02-full-final-referee'else'SELECTED-SOURCE-PATHS.json'))
    check({canon(k):v['sha256']for k,v in sm.items()}==canonical,'full independent exact35 source map '+name)
check('/root/ra02_full_final_referee'==review_manifests['RA02-full-final-referee']['reviewer'],'first nonauthor final referee identity')
check('/root/ie13_continuation'==review_manifests['RA02-ie13-final-local-development19']['reviewer'],'second nonauthor final referee identity')
oldlake=(W/'lakefile.toml').read_bytes()
check(oldlake.count(b'defaultTargets = ["Challenge"]')==1 and b'name = "Solution"'not in oldlake,'only necessary default and Solution library activation')
newlake=oldlake.replace(b'defaultTargets = ["Challenge"]',b'defaultTargets = ["Solution"]')+b'\n[[lean_lib]]\nname = "Solution"\n'
schema=bind(I/'docs/lean/schema/v0.4.schema.json',SCHEMA_SHA);validator=bind(I/'tools/lean/validate_manifest.py')

d=yaml.safe_load((W/'formalization.yaml').read_text())
d['repository']={'role':'substantive-development'}
d['project']['description']='Complete negative answer to the original RPCholesky polynomial trace-factor question. For every real C>0 and p>=0, a complex positive-definite matrix of order r+1 strictly violates the proposed bound after exactly r pivots. All normalized process and genuine ordered eigenvalue-tail semantics are proved.'
d['sources'][1]['note']='Original resolution credited to Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. This finite arrowhead proof establishes the sufficient factor 2^r/3, not the manuscript sharp limiting ratio, entrywise-positive, correlation-matrix or LU extensions.'
d['related_formalizations'] += [
 {'id':'https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474','relationship':'builds-on','note':'Actual complex PSD congruence, decreasing Hermitian spectrum, Euclidean Rayleigh infimum, finite sums/products and arbitrary-real-power asymptotics.'},
 {'id':'https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926','relationship':'builds-on','note':'One kernel-mode point certificate exp(1)<=3, consumed by the full tail-factor and final counterexample chain.'}]
d['automation']['methods'][0]['tool_setup']='Parallel proof and independent-referee agents. Actual local development used one coordinator-run macOS compiler, one thread and at most4096MiB per process, with pinned source-matched reuse. Fresh final non-root Linux kernel/Comparator/sandbox execution is a separate gate.'
d['automation']['notes']='Substantial OpenAI Codex assistance. The package preparer /root/mf22_publication_referee authored RA02 statements and most proof modules and is not an independent final referee. Other proof contributors are /root/mi04_independent_referee and /root; the two complete nonauthor final reviewers and exact scopes are retained separately. No official Tau Ceti endorsement or human peer review is claimed.'
d['status']={'scope':'Negates the original outer real C>0,p>=0 assertion for all positive dimensions, complex PSD matrices and integer1<=r<=n, with exactly r true RPCholesky steps and actual decreasing eigenvalue tail.','whole_problem_verified':False,'sorry_count':0,'sorry_in_definitions':0,'axioms':sorted(PERMITTED),'main_results':results,'source_scan_note':'All35 implementation files are hole-free. The27 deliberate Challenge placeholders belong only to the separate specification environment.'}
d['fidelity']['divergences']=d['fidelity']['divergences'].replace('The proposed proof uses','The proof uses')
d['review']={'status':'agent-reviewed complete source and actual local evidence; canonical Linux acceptance pending','reviewers':['/root/ra02_full_final_referee','/root/ie13_continuation'],'notes':'Both reviewers read all35 sources and the full original target and independently authenticated the local result. Their exact reports and scopes are in reviews/final. The package author is not an independent referee of the proof or this packaging. No official Tau Ceti or human endorsement is asserted.'}
d['alignment'].update(active_source_manifest='ACTIVE-SOURCE-MANIFEST.json',implementation_map='IMPLEMENTATION-MAP.json',publication_evidence='PUBLICATION-EVIDENCE.json',current_reading_note='README.md')
d['verification']={'phase':'Actual complete serial macOS source build accepted; canonical Linux verification pending','statement_elaboration':'Actual original run35083895041 Definitions/Challenge commands passed; full shared run failed elsewhere. Exact record retained.','proof_implementation':'All35 source inputs compiled successfully through actual development19, with3fresh commands and32source-matched reused successes.','canonical_verification_completed':False,'default_kernel':'pending fresh canonical Linux export/replay','comparator':'pending all27 actual comparisons','sandbox_and_rejection_controls':'pending actual non-root Linux controls','local_acceptance':'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json','local_acceptance_sha256':ACCEPTANCE_SHA,'local_receipt_sha256':a['receipt_sha256'],'permitted_axioms':sorted(PERMITTED),'observed_axioms':'All27 local output lists match propext, Classical.choice and Quot.sound.','numerical_certificate':{'declaration':'NLA.RA02.exp_one_bound','statement':'Real.exp1<=3','method':'interval_decide (trust := kernel)','consumed_by':['rank_denominator_le_three','exponential_tail_factor','universal_counterexamples','no_polynomial_trace_factor'],'interval_subdivision':'none; all rank, matrix, history and real-exponent arguments symbolic'},'publication':'Private source preparation only; no status/count/Git/CI/PR change.'}
jsonschema.Draft7Validator(read(schema)).validate(d)

# All source/acceptance/review guards have passed before output creation.
P.mkdir()
for k,v in rows.items():copy(v['source'],canon(k))
snap='statement-audit/frozen-35083895041/snapshots/'
for k,h in frozen.items():
    copy(W/k,snap+k)
    if k not in canonical and k!='lakefile.toml':copy(W/k,k)
put('lakefile.toml',newlake)
records=['SOURCE-PROVENANCE.json','STATEMENT-FREEZE.json','NUMERICAL-FIRST.json','PRIMARY-API.json','REUSE-AND-API.md','REUSE-AUDIT.json','REVIEW-PLAN.md','SEMANTIC-API-PROVENANCE.json','STANDARDS-PROVENANCE.json','DUPLICATE-AUDIT.json','MATHEMATICAL-PREFLIGHT.json','STATIC-CHECKS.json']
for fn in records:copy(W/fn,fn)
for fn in ['README.md','formalization.yaml','lakefile.toml']:copy(W/fn,'verification/packaging/historical-source/'+fn)
copy(W/'statement-history/DRAFT-MANIFEST.json','statement-history/DRAFT-MANIFEST.json')
dump('statement-history/ARCHIVE-SCOPE.json',{'scope':'Original draft inventory and planning documents retain historical wording. They are not current status, package inventory or new runtime claims. Exact amended frozen files and actual statement execution are retained separately.','actual_statement_commit':freeze['actual_statement_commit'],'actual_statement_run':freeze['actual_statement_run'],'original_pre_local_Lean_policy':'The earlier freeze prohibited local Lean. The user subsequently explicitly authorized local-first serial one-thread development with a4096MiB process limit; historical frozen text is preserved, not retroactively edited.'})
sr=B/'development-runs'/str(freeze['actual_statement_run'])
for src,rel in [(sr/'artifacts/lean-development-statements/receipt.json','receipt.json'),(sr/'ROOT-AUDIT.json','ROOT-AUDIT.json'),(B/'SF01-RA02-STATEMENT-ACCEPTANCE.json','COORDINATOR-ACCEPTANCE.json')]:copy(src,'statement-audit/runtime/'+rel)
# Preserve the bounded pre-existing source, standards, primary APIs and example records.
for src in sorted((W/'sources').rglob('*')):
    if src.is_file():reference(src,str(src.relative_to(W)))
for row in read(W/'SOURCE-PROVENANCE.json')['source_records']:
    bind(W/row['packet_path'],row['packet_sha256']);bind(row['raw_private_path'],row['raw_sha256'])
    if row['contact_redaction_only']:
        omitted.append({'original_path':row['raw_private_path'],'sha256':row['raw_sha256'],'immutable_source':'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/'+row['commit']+'/'+row['path'],'retained_contact_redacted_path':row['packet_path'],'retained_sha256':row['packet_sha256'],'reason':'One original contact string removed in the already labelled historical snapshot; all mathematical content preserved. Raw and redacted digests are distinct.'})
for field,key in [('STANDARDS-PROVENANCE.json','records'),('PRIMARY-API.json','files'),('SEMANTIC-API-PROVENANCE.json','retained'),('REUSE-AUDIT.json','patterns')]:
    for row in read(W/field)[key]:bind(W/row['packet_path'],row['sha256'])
copy(ACCEPTANCE,'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json')
copy(root_audit,'verification/local-development/audit.py')
runtime_paths.update([ASSEMBLY,L/'LOCAL-ENVIRONMENT.json',L/'serial_compile.py',L/'serial_compile_v2.py',L/'serial_compile_v3.py'])
pathmap={}
for src in sorted(runtime_paths):
    src=src.resolve();check(src.is_relative_to(L) and src.suffix in {'.json','.log','.py'},'text runtime retention '+str(src))
    rel='verification/local-development/'+str(src.relative_to(L));copy(src,rel);pathmap[str(src)]={'path':rel,'sha256':sha(src)}
dump('verification/local-development/PATH-MAP.json',pathmap)
dump('verification/local-development/SCOPE.json',{'scope':'Actual complete local19 receipt plus all successful original command logs/receipts and reuse-chain receipts from the root acceptance. Shared receipts truthfully retain unrelated historic errors. No cache binary is distributed; original successful output hashes remain in the unchanged acceptance and independent audits.','fresh_commands':3,'source_matched_reused_commands':32,'final_transitive_sources':35,'canonical_Linux_or_Comparator':False,'independent_execution_by_preparer':False})
review_records=[]
for name,manifest in review_manifests.items():
    q=B/'reviews'/name
    for fn in manifest['files']:copy(q/fn,'reviews/final/'+name+'/'+fn)
    copy(q/'MANIFEST.json','reviews/final/'+name+'/MANIFEST.json')
    review_records.append({'reviewer':manifest['reviewer'],'path':'reviews/final/'+name+'/REVIEW.md','manifest':'reviews/final/'+name+'/MANIFEST.json','manifest_sha256':REVIEWS[name],'scope':'Complete nonauthor source review plus independent audit of existing local evidence; no fresh compiler rerun, Linux or Comparator claim.'})
historical=[]
for name in ['RA02-root-statements','RA02-mi04-statements','RA02-ie13-Matrix-scope-20260916','RA02-mi04-Matrix-scope-20260916']:
    q=B/'reviews'/name
    for fn in ['REVIEW.md','CHECKS.json','MANIFEST.json']:
        if(q/fn).is_file():reference(q/fn,'reviews/statement-history/'+name+'/'+fn)
    historical.append({'path':'reviews/statement-history/'+name+'/REVIEW.md','scope':'Exact prior independent statement/scope review, preserving original date and limitations.'})
dump('reviews/INDEX.json',{'final_reviews':review_records,'statement_history':historical,'preparer_role':'RA02 statement/proof author and metadata preparer; not an independent referee of its proof or packaging.','canonical_runtime':'pending','official_Tau_Ceti_or_human_endorsement':False})
dump('ACTIVE-SOURCE-MANIFEST.json',{'problem_id':'RA-02','source_sha256':canonical,'retained_Lean_files':35,'final_transitive_import_closure':sorted(map(canon,seen)),'wrapper_transport':'NLA/RA02/Complete.lean -> Solution.lean, exact bytes','local_acceptance_sha256':ACCEPTANCE_SHA,'canonical_verification_completed':False,'whole_problem_verified':False})
dump('IMPLEMENTATION-MAP.json',{'exports':results,'source_sha256':canonical,'status':'Actual local source compilation accepted; fresh canonical Comparator identity pending'})
dump('verification/packaging/CONTRACT-HEADERS.json',{'scope':'Static whitespace-normalized header identity only, not Comparator execution','declarations':contract_map})
put('verification/packaging/LAKE-ACTIVATION.patch',''.join(difflib.unified_diff(oldlake.decode().splitlines(True),newlake.decode().splitlines(True),fromfile='frozen/lakefile.toml',tofile='active/lakefile.toml')))
dump('verification/packaging/TRANSITION.json',{'all35_Lean_bytes_unchanged':True,'only_filename_transport':'NLA/RA02/Complete.lean -> Solution.lean','frozen9_originals':frozen,'active_Lake_only_changes':['defaultTargets Challenge -> Solution','register the Solution Lean library required by that default'],'active_lake_sha256':hashlib.sha256(newlake).hexdigest(),'proof_pin_harness_resource_change':False,'Git_CI_publication_count_action':False})
dump('verification/OMITTED-ORIGINALS.json',{'privacy_omissions':omitted,'scope':'All active proofs, frozen contracts and actual successful command logs are retained. Raw contact-bearing references, raw GitHub payloads, huge public-tree archives and compiled caches remain private.'})
dump('PUBLICATION-EVIDENCE.json',{'phase':'Actual local development and two complete nonauthor source reviews accepted; private canonical candidate','local_acceptance':'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json','local_acceptance_sha256':ACCEPTANCE_SHA,'source_map':'ACTIVE-SOURCE-MANIFEST.json','review_index':'reviews/INDEX.json','canonical_verification_completed':False,'remaining_gates':['independent canonical package review','fresh non-root Linux default-kernel/Comparator/axiom/LeanCert/control verification','actual runtime source authentication and referees','publication documents and exact publication commit rerun','individual upstream main PR and its actual CI'],'status_count_or_publication_change':False})
put('formalization.yaml','# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+yaml.safe_dump(d,sort_keys=False,allow_unicode=True,width=100))
put('README.md','''# RA-02 Lean formalization

This candidate disproves the original polynomial trace-error guarantee after exactly the target rank of randomly pivoted Cholesky steps. For every real C>0 and p>=0, it constructs a positive-definite complex matrix of dimension r+1 whose actual expected residual trace after r steps strictly exceeds C r^p times its actual ordered eigenvalue tail. The universal target includes every positive dimension, every complex Hermitian PSD matrix, and every integer1<=r<=n.

**Actual local Lean build and two independent complete source reviews accepted; canonical Linux verification pending.** The [local acceptance](verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json) and [original command map](verification/local-development/PATH-MAP.json) identify all35 successful source-matched origins. Development19 compiled three modules afresh and reused32 exact prior successful outputs. These records do not certify unrun Linux default-kernel replay, Comparator or sandbox/rejection controls. No verification count, publication commit or PR is claimed by this private candidate.

Start with the [numerical targets](NUMERICAL_TARGETS.md), concrete [Definitions](NLA/RA02/Definitions.lean), independent [Challenge](Challenge.lean), and [source correspondence](SourceCorrespondence.md). The [active source manifest](ACTIVE-SOURCE-MANIFEST.json) and [implementation map](IMPLEMENTATION-MAP.json) identify all35 files and27 exports. Original frozen preparation documents retain their historical pending wording; [current evidence](PUBLICATION-EVIDENCE.json) records the current phase. Deliberate Challenge placeholders are separate specifications and are never imported by the proof.

The proof establishes the normalized adaptive PSD process, including zero residuals, zero-probability choices and every ordered history. It uses genuinely decreasing Hermitian eigenvalues and a Euclidean Rayleigh bound. A finite arrowhead family, exact residual identities and an injective binary history count give a sufficient factor2^r/3. This negates the full original question. The manuscript's sharper limiting factor2^r, entrywise-positive and correlation-matrix extensions, the separate LU theorem, and oversampling are not formal claims here.

The sole numerical certificate, `Real.exp 1 <= 3`, uses LeanCert kernel trust. Its result feeds the rank-dependent denominator bound, actual spectral-tail factor, and final arbitrary-real-exponent contradiction. All matrix, rank, history and exponent calculations remain symbolic; there is no interval subdivision or numerical eigenvalue approximation.

[Solution](Solution.lean) is byte-identical to the final locally tested Complete wrapper. Its import closure reaches all34 mathematical files. All nine original frozen files are retained as exact snapshots; active Lake configuration only registers and selects Solution. With pinned dependencies available, `lake build` in this directory is the local entry point. Fresh canonical Linux verification of this packaging is still pending. Development followed the user's local-first instruction: one compiler process, one thread, at most4096MiB, and only pinned source-matched successful output reuse.

From the repository root, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-02/lean /absolute/path/to/nla-lean-tools
```

Formalization and integration: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical resolution: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. RPCholesky and the comparison problem retain the credit to Chen, Epperly, Tropp and Webber. Substantial OpenAI Codex assistance is disclosed; no new historical-priority claim is made.

Both [complete nonauthor reviews](reviews/INDEX.json) read every selected proof file and authenticate the recorded local evidence. The package preparer authored RA-02 statements and proofs, so its packaging checks are not an independent mathematical review. Reviewer scopes and roles are explicit; no official Tau Ceti endorsement or human peer review is asserted. Mathlib and LeanCert supply proof foundations; Schiffer and Forsythe supplied inspected structure examples. The [bounded duplicate audit](DUPLICATE-AUDIT.json) is a dated public snapshot, not a claim about unpublished or later work. [Source/privacy records](verification/OMITTED-ORIGINALS.json) distinguish raw and contact-redacted manuscript hashes. [License](LICENSE).
''')
copy(schema,'verification/packaging/v0.4.schema.json')
copy(Path(__file__),'verification/packaging/prepare.py')
dump('verification/RETAINED-PATHS.json',retained)
validated=subprocess.run([sys.executable,str(validator),str(P)],capture_output=True,text=True)
put('verification/packaging/schema-validation.log',validated.stdout+validated.stderr)
check(validated.returncode==0,'actual shared schema and27-export coverage validation')
for k,h in canonical.items():check(sha(P/k)==h,'final unchanged active source '+k)
for k,h in frozen.items():check(sha(P/(snap+k))==h,'final frozen snapshot '+k)
for p in P.rglob('*'):
    if p.is_file():check(EMAIL.search(p.read_bytes())is None,'final no email '+str(p.relative_to(P)))
dump('PACKAGE-MANIFEST.json',{'phase':'complete local development and two complete source reviews accepted; canonical verification pending','files':{str(p.relative_to(P)):sha(p)for p in sorted(P.rglob('*'))if p.is_file()}})
H.mkdir()
(H/'CHECKS.json').write_text(json.dumps({'preparer':'/root/mf22_publication_referee','role':'RA02 proof/statement author; not independent mathematical or package reviewer','checks':checks,'package_manifest_sha256':sha(P/'PACKAGE-MANIFEST.json'),'schema_exit_code':validated.returncode,'new_Lean_execution':False,'Git_network_or_count_action':False},indent=2)+'\n')
(H/'BINDINGS.json').write_text(json.dumps({os.path.relpath(p,H):h for p,h in bindings.items()},indent=2)+'\n')
(H/'HANDOFF.md').write_text('''# RA-02 private canonical package handoff

All35 actual accepted source bytes, all27 exported contracts and nine original frozen snapshots are preserved. Complete becomes Solution by identical byte transport. The only active Lake changes register Solution and make it the default. Original dependencies, proof options, trust settings and target remain unchanged.

Actual serial macOS development19 has three fresh successful commands and32 authenticated prior successes. Both complete nonauthor final reviews are retained with exact manifests. This preparer authored RA02 statements and proofs and does not claim independent mathematical approval. Fresh canonical Linux default-kernel/Comparator/sandbox/rejection controls, publication-head execution and the upstream PR remain pending.

Python preparation ran only source/hash/privacy/schema checks. It did not invoke Lean, Lake, Git, network tools, publication, or a verification count change. Compiled caches are not copied. Historical planning text is preserved and explicitly distinguished from active status.
''')
(H/'MANIFEST.json').write_text(json.dumps({'files':{p.name:sha(p)for p in sorted(H.iterdir())if p.is_file()},'preparer':{'path':str(Path(__file__).resolve()),'sha256':sha(__file__)},'package_manifest_sha256':sha(P/'PACKAGE-MANIFEST.json')},indent=2)+'\n')
print(json.dumps({'package_manifest':sha(P/'PACKAGE-MANIFEST.json'),'handoff_manifest':sha(H/'MANIFEST.json'),'checks':len(checks),'input_bindings':len(bindings),'compiler_Git_network_execution':False},indent=2))
