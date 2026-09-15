from pathlib import Path
import hashlib,json,re,subprocess
repo=Path('/private/tmp/nla-formalization-sp05-20260915');p=repo/'eigenvalues-and-inverse-problems/SP-05/lean';s=Path(__file__).parent
expected=json.loads((p/'reviews/statement-inputs.json').read_text());base=expected['published_base'];checks=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def check(n,c):assert c,n;checks.append(n)
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
check('ten exact proposed boundary files',len(expected['input_sha256'])==10)
for f,h in expected['input_sha256'].items():
    check('current boundary '+f,sha((p/f).read_bytes())==h)
    check('fresh snapshot boundary '+f,sha((s/f).read_bytes())==h)
source=json.loads((p/'reviews/initial/source-hashes.json').read_text())
for f,h in source['sha256'].items():
    check('source hash '+f,sha((repo/f).read_bytes())==h)
    check('source preserved at published base '+f,(repo/f).read_bytes()==git('show',base+':'+f))
check('unchanged 217 ID registry',(repo/'problem_ids.json').read_bytes()==git('show',base+':problem_ids.json') and len(json.loads((repo/'problem_ids.json').read_text()))==217)
text=(repo/'eigenvalues-and-inverse-problems/SP-05/solution.md').read_text().replace('\r\n','\n').replace('\r','\n');block=text[text.index('## Theorem '):text.index('## Scope and review notes')].strip().encode()
check('original historical proof block',len(block)==3483 and sha(block)=='54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42')
check('canonical remains Solved','**Status:** Solved  ' in (p.parent/'README.md').read_text())
check('Solution definitions only',[x.strip() for x in (p/'Solution.lean').read_text().splitlines() if x.strip() and not x.strip().startswith('--')]==['import NLA.SP05.Definitions'])
check('no proof modules',list((p/'NLA/SP05').glob('*.lean'))==[p/'NLA/SP05/Definitions.lean'])
challenge=(p/'Challenge.lean').read_text();defs=(p/'NLA/SP05/Definitions.lean').read_text();conf=json.loads((p/'comparator.json').read_text())
check('six exact exported signatures',conf['theorem_names']==['NLA.SP05.'+x for x in re.findall(r'^theorem (\w+)',challenge,re.M)] and len(conf['theorem_names'])==6)
check('six expected Challenge placeholders',len(re.findall(r'^  sorry$',challenge,re.M))==6)
check('no definition holes',conf['definition_names']==[] and re.search(r'\b(sorry|axiom|admit|native_decide)\b',defs) is None)
check('correct permitted axioms',conf['permitted_axioms']==['propext','Classical.choice','Quot.sound'])
log=(s/'challenge-build.log').read_text();api=(s/'boundary-audit.log').read_text()
check('independent fresh Challenge compile','Build completed successfully (2710 jobs).' in log and log.count('declaration uses `sorry`')==6 and 'error:' not in log)
check('independent API and expanded boundary compile','error:' not in api and 'Matrix.PosDef' in api and 'CFC.sqrt_unique' in api and 'PiLp.innerProductSpace fun x => ℂ' in api)
check('audit has no implementation declarations',re.search(r'^\s*(theorem|lemma|def|axiom|example)\b',(s/'BoundaryAudit.lean').read_text(),re.M) is None)
version=subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version']).decode().strip()
check('pinned actual compiler','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
packages=[]
for q in json.loads((p/'lake-manifest.json').read_text())['packages']:
    path=s/'.lake/packages'/q['name'];head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD']).decode().strip();dirty=subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no']).decode()
    check('pinned dependency '+q['name'],head==q['rev']);check('tracked clean dependency '+q['name'],not dirty);packages.append({'name':q['name'],'commit':head,'tracked_clean':not dirty})
diagnostic=json.loads((s/'independent-exact.json').read_text());check('177 independently authored exact diagnostics',diagnostic['result']=='PASS' and diagnostic['checks_count']==177 and diagnostic['contributor_checker_imported_or_executed'] is False)
api_files=['Mathlib/LinearAlgebra/Matrix/Vec.lean','Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/Order.lean','Mathlib/Analysis/InnerProductSpace/Rayleigh.lean','Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean','Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean','Mathlib/Order/Bounds/Defs.lean']
report={'reviewer':'/root/reference_api_review, independent OpenAI GPT-6 Codex AI; no proof implementation','phase':'exact pre-proof statement review','result':'APPROVE','published_base':base,'worktree_HEAD':git('rev-parse','HEAD').decode().strip(),'input_sha256':expected['input_sha256'],'source_sha256':source['sha256'],'historical_proof_block_sha256':sha(block),'additional_preparation_files_sha256':{f:sha((p/f).read_bytes()) for f in ['README.md','Solution.lean','reviews/initial/ApiProbe.lean','reviews/initial/ApiProbe.log']},'checks_count':len(checks),'checks':checks,'compiler':version,'dependencies':packages,'reviewed_mathlib_files_sha256':{f:sha((s/'.lake/packages/mathlib'/f).read_bytes()) for f in api_files},'commands':[{'command':'lake build Challenge','exit':0,'jobs':2710,'intentional_holes':6},{'command':'lake env lean BoundaryAudit.lean','exit':0,'proof_implementation':False},{'command':'python3 independent-exact.py','exit':0,'diagnostic_checks':177}],'limits':['This approves exact statements and a mathematically valid plan; no target has yet been proved.','No Solution proof build, permitted-axiom closure, LeanCert execution/consumption, Comparator or authoritative Linux result is claimed.','No new literature-completeness search, novelty claim, external human review or official Tau Ceti endorsement.']}
(s/'audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'result':'APPROVE','checks':len(checks),'audit_sha256':sha((s/'audit.json').read_bytes())}))
