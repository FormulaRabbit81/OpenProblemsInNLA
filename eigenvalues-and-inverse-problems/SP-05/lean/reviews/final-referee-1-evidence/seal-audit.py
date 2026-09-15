from pathlib import Path
import hashlib,json,re,subprocess,sys
repo=Path('/private/tmp/nla-formalization-sp05-20260915');p=repo/'eigenvalues-and-inverse-problems/SP-05/lean';s=Path(__file__).parent
candidate=sys.argv[1];prefix='eigenvalues-and-inverse-problems/SP-05/lean/'
base='d8c38a795876b132c90df8d1be8682d3dcde394c';preproof='04d1de395494800390405f3df1645316fe7943c2'
checks=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def ck(n,c):assert c,n;checks.append(n)
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
ck('exact candidate HEAD',git('rev-parse','HEAD').decode().strip()==candidate)
seal=json.loads((p/'reviews/final-source-inputs.json').read_text());inputs=seal['input_sha256']
for f,h in inputs.items():
 ck('current exact reviewed source '+f,sha((p/f).read_bytes())==h)
 ck('committed exact reviewed source '+f,sha(git('show',candidate+':'+prefix+f))==h)
snapshot=json.loads((s/'snapshot-inputs.json').read_text())
for f,h in snapshot.items():ck('independently compiled snapshot '+f,sha((p/f).read_bytes())==sha((s/f).read_bytes())==h)
frozen=json.loads((p/'reviews/statement-freeze.json').read_text())
ck('10 pre-proof boundary inputs',len(frozen['input_sha256'])==10)
for f,h in frozen['input_sha256'].items():
 ck('frozen bytes current '+f,sha((p/f).read_bytes())==h)
 ck('frozen bytes before proof '+f,sha(git('show',preproof+':'+prefix+f))==h)
for f,h in frozen['independent_statement_reports'].items():ck('independent statement approval unchanged '+f,sha((p/f).read_bytes())==h)
source=json.loads((p/'reviews/initial/source-hashes.json').read_text())
for f,h in source['sha256'].items():ck('complete original source preserved '+f,sha((repo/f).read_bytes())==h and (repo/f).read_bytes()==git('show',base+':'+f))
text=(p.parent/'solution.md').read_text().replace('\r\n','\n').replace('\r','\n');block=text[text.index('## Theorem '):text.index('## Scope and review notes')].strip().encode()
ck('original reviewed mathematical proof block',len(block)==3483 and sha(block)=='54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42')
ck('canonical still Solved','**Status:** Solved  ' in (p.parent/'README.md').read_text())
ck('registry all 217 IDs preserved',(repo/'problem_ids.json').read_bytes()==git('show',base+':problem_ids.json') and len(json.loads((repo/'problem_ids.json').read_text()))==217)
challenge=(p/'Challenge.lean').read_text();proof=(p/'NLA/SP05/Proof.lean').read_text();config=json.loads((p/'comparator.json').read_text())
def signatures(text):return {m.group(1):re.sub(r'\s+',' ',m.group(2)).strip() for m in re.finditer(r'^theorem (\w+)(.*?):= by',text,re.M|re.S)}
ck('all six literal public signatures identical to independent Challenge',signatures(challenge)==signatures(proof) and len(signatures(proof))==6)
ck('exact Comparator selection all six',config['theorem_names']==['NLA.SP05.'+n for n in signatures(challenge)])
ck('no definition holes and exact permitted axioms',config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound'])
ck('proof solution imports actual Proof only',(p/'Solution.lean').read_text().strip()=='import NLA.SP05.Proof')
for f in (p/'NLA/SP05').glob('*.lean'):
 src=f.read_text();ck('no admissions unsafe or custom axioms '+f.name,re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',src) is None)
 ck('no Challenge import '+f.name,re.search(r'^import .*Challenge',src,re.M) is None)
ck('explicit kernel numerical certificate','interval_decide (trust := kernel)' in (p/'NLA/SP05/Certificates.lean').read_text())
ck('consumed witness positivity certificate','exact skew_norm_positive_certificate' in (p/'NLA/SP05/Basic.lean').read_text())
ck('actual witness enters attained skew minimum','skew_ne_zero n hn' in (p/'NLA/SP05/Sectors.lean').read_text() and 'skew_sector_nonempty n hn' in (p/'NLA/SP05/Sectors.lean').read_text())
challenge_log=(s/'referee-challenge-build.log').read_text();solution_log=(s/'referee-solution-build.log').read_text();audit_log=(s/'referee-full-audit.log').read_text()
ck('fresh independent Challenge 2710 jobs six deliberate holes','Build completed successfully (2710 jobs).' in challenge_log and challenge_log.count('declaration uses `sorry`')==6 and 'error:' not in challenge_log)
ck('fresh independent Solution 3738 jobs no holes','Build completed successfully (3738 jobs).' in solution_log and 'declaration uses `sorry`' not in solution_log and 'error:' not in solution_log)
ck('only two harmless exact-wrapper unused assumption warnings',len(re.findall(r'^warning:',solution_log,re.M))==2 and 'Variable name `hA`' in solution_log and 'Variable name `hB`' in solution_log)
closures=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit_log)
without=re.findall(r"'([^']+)' does not depend on any axioms",audit_log)
ck('fresh reviewer exact types/kernel audit compile','error:' not in audit_log and 'warning:' not in audit_log)
allnames=json.loads((s/'audited-declarations.json').read_text());ck('all 81 actual project theorem declarations checked',len(allnames)==81 and all('NLA.SP05.'+n in [x[0] for x in closures]+without for n in allnames))
ck('six literal wrappers plus two nonvacuity instantiations also checked',len(closures)+len(without)==89)
for name,axioms in closures:ck('permitted transitive closure '+name,set(axioms.split(', '))<={'propext','Classical.choice','Quot.sound'})
version=subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version']).decode().strip()
ck('actual pinned compiler','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
packages=[]
for dep in json.loads((p/'lake-manifest.json').read_text())['packages']:
 path=s/'.lake/packages'/dep['name'];head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD']).decode().strip();dirty=subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no']).decode()
 ck('pinned dependency '+dep['name'],head==dep['rev']);ck('tracked clean dependency '+dep['name'],not dirty);packages.append({'name':dep['name'],'commit':head,'tracked_clean':not dirty})
diagnostics=json.loads((s/'independent-exact.json').read_text());ck('183 independent exact arithmetic checks',diagnostics['result']=='PASS' and diagnostics['checks_count']==183 and not diagnostics['contributor_checker_imported_or_executed'])
ck('metadata6 schema coverage passes','PASS (6 declarations)' in (s/'metadata-validation.log').read_text())
api=['Mathlib/LinearAlgebra/Matrix/Vec.lean','Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/Order.lean','Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean','Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean','Mathlib/Order/Bounds/Defs.lean']
result={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent non-implementing AI','phase':'complete source review; authoritative Linux/Comparator pending','result':'PASS','candidate_commit':candidate,'published_base':base,'preproof_commit':preproof,'candidate_inputs_sha256':inputs,'candidate_input_seal_sha256':sha((p/'reviews/final-source-inputs.json').read_bytes()),'frozen_inputs_sha256':frozen['input_sha256'],'source_sha256':source['sha256'],'source_proof_block_sha256':sha(block),'literal_public_signatures':signatures(proof),'checks_count':len(checks),'checks':checks,'fresh_snapshot_inputs_sha256':snapshot,'actual_compiler':version,'dependencies':packages,'all_theorem_closures':{n:[] for n in without}|{n:x.split(', ') for n,x in closures},'reviewed_mathlib_source_sha256':{f:sha((s/'.lake/packages/mathlib'/f).read_bytes()) for f in api},'fresh_builds':{'Challenge':{'exit':0,'jobs':2710,'deliberate_placeholders':6},'Solution':{'exit':0,'jobs':3738,'proof_holes':0},'AuditFull.lean':{'exit':0,'kernel_assertions_and_axiom_closures':89}},'independent_exact_diagnostic_checks':183,'authoritative_Linux_or_Comparator_run_performed':False,'limits':['Local fresh project source builds reuse pinned dependency .olean cache; no project .olean cache was reused.','Literal source signatures and independent elaboration checked locally; actual isolated Comparator and Linux operation remain pending.','Independent AI review; no external human review or official endorsement.']}
(s/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'result':'PASS','checks':len(checks),'candidate_inputs':len(inputs),'closures':89}))
