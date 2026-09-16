from pathlib import Path
import hashlib,json,subprocess,os,importlib.util
B=Path('/tmp/nla-lean-next-20260915');W=Path('/private/tmp/nla-lean-next-ie13-worktree');P=B/'IE13-canonical-package-v2';O=Path(__file__).resolve().parent
head='032d4c86c52ffde0c4d440f28527ba43555a0a24';seed='6b626a5b4ad567cd0d6edaaf53b36870ed5b6cdc';base='ce47b5630bf3680d9211131c3a43825b022c139a';project='linear-systems-and-elimination/IE-13/lean'
S=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();H=lambda d:hashlib.sha256(d).hexdigest();J=lambda p:json.loads(p.read_text())
os.environ['GIT_OPTIONAL_LOCKS']='0'
def git(*a):return subprocess.check_output(['git','-c','gc.auto=0','-C',str(W),*a])
assert git('rev-parse',head+'^').decode().strip()==seed and git('rev-parse',seed+'^').decode().strip()==base
assert git('rev-parse',seed+'^{tree}')==git('rev-parse',base+'^{tree}')
pkg=dict(J(P/'PACKAGE-MANIFEST.json')['files']);pkg['PACKAGE-MANIFEST.json']=S(P/'PACKAGE-MANIFEST.json');assert len(pkg)==95
assert S(B/'IE13-CANONICAL-COMMIT-CHECK.json')=='2e6fa3f46c4d8382aec6cb2cde702c875ad138c8526049d9bab99c6df847d117'
assert J(B/'IE13-CANONICAL-COMMIT-CHECK.json')['files']==pkg
assert set(git('diff','--name-only',seed,head).decode().splitlines())=={project+'/'+n for n in pkg}
assert git('diff','--diff-filter=D','--name-only',seed,head)==b''
for n,h in pkg.items():assert H(git('show',head+':'+project+'/'+n))==S(P/n)==h,n
for prefix in ['tools/lean','docs/lean/schema','.github/workflows/lean-verification.yml','problem_ids.json','linear-systems-and-elimination/IE-13/README.md','RESOLVED.md']:
 assert git('diff',base,head,'--',prefix)==b''
raw=git('cat-file','commit',head)
for line in raw.splitlines():
 if line.startswith((b'author ',b'committer ')):assert b' <>' in line
# Load only the byte-identical shared selector, then inspect immutable trees.
selector=Path('/tmp/nla-lean-next-mf22-worktree/tools/lean/projects.py');assert selector.read_bytes()==git('show',head+':tools/lean/projects.py')
spec=importlib.util.spec_from_file_location('unchanged_selector',selector);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
a=module.discover_at_ref(W,seed);b=module.discover_at_ref(W,head);module.require_retained_projects(b,a)
selected=module.select(b,git('diff','--name-only',seed,head).decode().splitlines());assert len(a)==34 and len(b)==35 and selected==[{'id':'IE-13','project':project}]
prior=B/'reviews/IE13-staged-integration-mi04';assert S(prior/'MANIFEST.json')=='edd4a0db8b006bfee2eb70bb1094c48370ab832fc80d101df1de087c2bbddf8c'
for n,h in J(prior/'MANIFEST.json')['files'].items():assert S(prior/n)==h
pins={n:H(git('show',head+':'+n)) for n in ['tools/lean/harness.py','tools/lean/source-lock.json','tools/lean/projects.py','tools/lean/validate_manifest.py','.github/workflows/lean-verification.yml']}
for n,h in pins.items():assert S(Path('/tmp/nla-lean-next-mf22-worktree')/n)==h
result={'reviewer':'/root/mi04_independent_referee','actual_completed_scope':'independent literal-commit source/selection check only','commit':head,'parent':seed,'published_base':base,'all95_inputs_checked':True,'all27_math_and_28_contracts_match_approved_package':True,'all_protected_files_and_pins_unchanged':True,'prior_full_tree_projects':len(a),'current_full_tree_projects':len(b),'actual_Git_tree_selection':selected,'physical_sparse_CLI_not_executed_or_claimed_successful':True,'empty_author_and_committer_email':True,'pending_actual_run':35081003513,'runtime_acceptance':False,'pins':pins,'files':pkg,'local_Lean_Git_mutation_count_change':False}
(O/'COMMITTED-SOURCE-CHECKS.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('PASS literal commit source checks: 95 inputs; parent/seed tree; protected pins; immutable-tree selector retains34 and selects only IE13 among35; runtime remains pending.')
