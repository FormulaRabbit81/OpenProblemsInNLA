from pathlib import Path
import hashlib, json, re, subprocess

repo=Path('/private/tmp/nla-formalization-sp04-20260915')
rel=Path('eigenvalues-and-inverse-problems/SP-04/lean')
p=repo/rel
scratch=Path(__file__).parent
candidate='6c351ae4a147efb82a2ede9ebc604de0683105c4'
base='d8c38a795876b132c90df8d1be8682d3dcde394c'
checks=[]
def check(name, condition):
    assert condition,name
    checks.append(name)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
final=json.loads((p/'reviews/final-source-inputs.json').read_text())['input_sha256']
freeze=json.loads((p/'reviews/statement-freeze.json').read_text())
check('candidate commit',git('rev-parse','HEAD').decode().strip()==candidate)
for f,h in final.items():
    check('current final input '+f,sha((p/f).read_bytes())==h)
    check('candidate final input '+f,sha(git('show',candidate+':'+str(rel/f)))==h)
    check('independent snapshot '+f,sha((scratch/f).read_bytes())==h)
for f,h in freeze['input_sha256'].items():
    check('frozen statement input '+f,sha((p/f).read_bytes())==h)
    check('candidate frozen statement '+f,sha(git('show',candidate+':'+str(rel/f)))==h)
    check('pre-proof commit input '+f,sha(git('show','623e14e6:'+str(rel/f)))==h)
for f,h in freeze['independent_statement_reports'].items():
    check('unchanged pre-proof independent approval '+f,sha((p/f).read_bytes())==h)
sourcefiles=['eigenvalues-and-inverse-problems/SP-04/README.md','eigenvalues-and-inverse-problems/SP-04/solution.md','eigenvalues-and-inverse-problems/SP-04/solution.tex','references/colbrook-2026-09-11/verification/reviews/SP-04-review.md','problem_ids.json']
sourcehashes={}
for f in sourcefiles:
    b=(repo/f).read_bytes();sourcehashes[f]=sha(b)
    for ref in [candidate,base,'8f04b905eb2e0827b6b84f37d9d080ae1f05b202']:
        check('original preservation '+ref+' '+f,b==git('show',ref+':'+f))
md=(repo/sourcefiles[1]).read_text();block=md[md.index('## Theorem '):md.index('## Scope and review notes')].strip().encode()
check('historical exact mathematical block',len(block)==4714 and sha(block)=='77b6c6240eab1eab1cd7f9326a95a4bb7455188f951c11718c1b8c07cf691d95')
check('canonical remains Solved','**Status:** Solved  ' in (repo/sourcefiles[0]).read_text())
deps=[]
manifest=json.loads((p/'lake-manifest.json').read_text())
for pkg in manifest['packages']:
    d=scratch/'.lake/packages'/pkg['name']
    head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD']).decode().strip()
    diff=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no']).decode()
    check('pinned package '+pkg['name'],head==pkg['rev'])
    check('clean tracked package '+pkg['name'],diff=='')
    deps.append({'name':pkg['name'],'commit':head,'tracked_clean':not diff})
version=subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version']).decode().strip()
check('compiler version','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
cb=(scratch/'referee-challenge-build.log').read_text();sb=(scratch/'referee-solution-build.log').read_text();ab=(scratch/'referee-full-audit.log').read_text()
check('fresh Challenge success','Build completed successfully (2386 jobs).' in cb)
check('Challenge exactly eleven deliberate holes',cb.count('declaration uses `sorry`')==11)
check('fresh Solution success','Build completed successfully (3693 jobs).' in sb)
check('Solution no sorry warning','declaration uses `sorry`' not in sb)
check('local audit no errors','error:' not in ab)
allowed={'propext','Classical.choice','Quot.sound'}
def axiom_entries(log):return re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
axioms=axiom_entries(ab)
check('audit has all 33 expected closure results',len(axioms)==33)
for name,alist in axioms:
    actual={x.strip() for x in alist.split(',') if x.strip()}
    check('permitted transitive axioms '+name,actual<=allowed)
names=json.loads((p/'comparator.json').read_text())['theorem_names']
check('Comparator exactly eleven entries',len(names)==11 and len(set(names))==11)
check('Comparator no definition holes',json.loads((p/'comparator.json').read_text())['definition_names']==[])
for n in names:
    check('fresh Solution public closure '+n,n in dict(axiom_entries(sb)))
    check('literal frozen type assignment '+n,('Referee1.exact_'+n.split('.')[-1]) in dict(axioms))
proofs=list((p/'NLA/SP04').glob('*.lean'))+[p/'Solution.lean']
for f in proofs:
    content=f.read_text()
    clean=re.sub(r'/\-.*?\-/','',content,flags=re.S)
    clean=re.sub(r'--[^\n]*','',clean)
    check('no forbidden source escape '+f.name,re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',clean) is None)
cert=(p/'NLA/SP04/Certificates.lean').read_text()
check('four kernel interval certificate goals',cert.count('interval_decide (trust := kernel)')==3 and 'constructor <;> interval_decide' in cert)
uses={f.name:re.findall(r'scalar_numerical_bounds(?:\.[12])*',f.read_text()) for f in proofs if f.name!='Certificates.lean'}
check('certificate consumed in discriminant, root bound, product and endpoint',set(uses['ScalarPositive.lean'])=={'scalar_numerical_bounds.1','scalar_numerical_bounds.2.1','scalar_numerical_bounds.2.2.1'} and 'scalar_numerical_bounds.2.2.2' in uses['ScalarRoots.lean'])
diag=json.loads((scratch/'independent-arithmetic.json').read_text())
check('independent diagnostic rerun',diag['result']=='PASS' and diag['checks_count']==49 and diag['source_checker_imported_or_executed'] is False)
api={}
for f in ['Mathlib/Algebra/MvPolynomial/Funext.lean','Mathlib/Analysis/Matrix/Spectrum.lean','Mathlib/LinearAlgebra/Matrix/SchurComplement.lean','Mathlib/Algebra/Polynomial/Roots.lean','Mathlib/Topology/Instances/Matrix.lean']:
    api['mathlib/'+f]=sha((scratch/'.lake/packages/mathlib'/f).read_bytes())
report={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review (independent AI; no proof implementation)','phase':'final source and independent local kernel/type/trust audit; Linux/Comparator pending','candidate':candidate,'published_base':base,'result':'PASS','checks_count':len(checks),'checks':checks,'final_input_sha256':final,'preproof_input_sha256':freeze['input_sha256'],'source_context_sha256':sourcehashes,'reviewed_api_sha256':api,'compiler':version,'dependencies':deps,'closure_results':dict(axioms),'proof_source_files':[str(f.relative_to(p)) for f in proofs],'diagnostics':'49 independently authored rational diagnostics rerun; retained output carries historical preproof scope wording; universal proofs separately inspected and rebuilt','fresh_commands':[{'command':'lake build Challenge','exit':0,'jobs':2386},{'command':'lake build Solution','exit':0,'jobs':3693},{'command':'lake env lean AuditFull.lean','exit':0},{'command':'python3 independent-arithmetic.py','exit':0},{'command':'/private/tmp/nla-lean-audit-python/bin/python tools/lean/validate_manifest.py eigenvalues-and-inverse-problems/SP-04/lean','exit':0}],'local_dependencies':'Shared hash-pinned dependency cache only; fresh scratch project has no reused project artifacts','limitations':['No authoritative isolated Linux run or actual Comparator run performed here.','This is independent AI source review, not external human peer review or official Tau Ceti review.']}
(scratch/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'result':'PASS','checks':len(checks),'audit_sha256':sha((scratch/'audit.json').read_bytes())}))
