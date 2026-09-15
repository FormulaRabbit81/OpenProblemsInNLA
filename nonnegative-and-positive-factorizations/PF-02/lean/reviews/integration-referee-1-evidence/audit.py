from pathlib import Path
import collections,hashlib,importlib.util,json,re,subprocess,sys
from unittest.mock import patch
repo=Path('/private/tmp/nla-formalization-pf02-20260915')
scratch=Path(__file__).parent
commit='a36c4048982951fd73445b9e65493973f7460ed8'
publication='7b0c845628c61ab148ecf367fee1eb90c68f2649'
incoming='d8c38a795876b132c90df8d1be8682d3dcde394c'
oldbase='8f04b905eb2e0827b6b84f37d9d080ae1f05b202'
prefix='nonnegative-and-positive-factorizations/PF-02/'
checks=[]
def check(n,c):assert c,n;checks.append(n)
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
def sha(b):return hashlib.sha256(b).hexdigest()
def tree(ref):
    out={}
    for line in git('ls-tree','-r','-z',ref).split(b'\0'):
        if not line:continue
        meta,path=line.split(b'\t');out[path.decode()]=meta.decode()
    return out
t=tree(commit);before=tree(publication);main=tree(incoming)
check('exact current merge',git('rev-parse','HEAD').decode().strip()==commit)
check('exact parents',git('show','-s','--format=%P',commit).decode().strip()==publication+' '+incoming)
check('exact tree',git('rev-parse',commit+'^{tree}').decode().strip()=='0bb5a3db6f6037e20bacd9bd55592887c49c8a34')
check('exact current published base',git('rev-parse','origin/main').decode().strip()==incoming)
protected={f:sha((repo/f).read_bytes()) for f in before if f.startswith(prefix)}
check('all 121 PF02 published files retained',len(protected)==121 and {f for f in t if f.startswith(prefix)}==set(protected))
for f in protected:
    check('PF02 unchanged Git metadata '+f,t[f]==before[f])
    check('PF02 current bytes '+f,(repo/f).read_bytes()==git('show',publication+':'+f))
index={'README.md','CATALOG.md','nonnegative-and-positive-factorizations/README.md'}
changed=[f for f in set(t)|set(main) if t.get(f)!=main.get(f)]
check('only PF02 and its three indexes differ from main',all(f.startswith(prefix) or f in index for f in changed))
for f in main:
    if f.startswith(prefix) or f in index:continue
    check('incoming preserved '+f,t.get(f)==main[f])
incoming_changes=git('diff','--name-only',oldbase,incoming).decode().splitlines()
check('268 incoming changed paths',len(incoming_changes)==268)
adjusted=[]
for f in incoming_changes:
    if t.get(f)!=main.get(f):adjusted.append(f)
check('only two incoming changed paths need totals resolution',set(adjusted)=={'README.md','CATALOG.md'})
registry=json.loads((repo/'problem_ids.json').read_text())
check('registry exact all parents',len(registry)==217 and t['problem_ids.json']==before['problem_ids.json']==main['problem_ids.json'])
counts=collections.Counter()
for ident,f in registry.items():
    content=(repo/f).read_text();counts[re.search(r'^\*\*Status:\*\*\s+(.+?)\s*$',content,re.M).group(1)]+=1
    check('canonical preserved '+ident,(repo/f).read_bytes()==git('show',(publication if ident=='PF-02' else incoming)+':'+f))
check('exact integrated counts',dict(counts)=={'Lean verified':35,'Solved':69,'Open':42,'Partially resolved':71})
for f in index:
    text=git('show',incoming+':'+f).decode()
    text=text.replace('70 solved (published or independently audited); 34 solved with Lean verification.','69 solved (published or independently audited); 35 solved with Lean verification.')
    lines=text.splitlines(keepends=True)
    text=''.join(line.replace('**✅ SOLVED**','**🏆 LEAN VERIFIED**') if line.startswith('| [PF-02](') else line for line in lines)
    check('exact expected generated index '+f,text.encode()==(repo/f).read_bytes())
sys.path.insert(0,str(repo/'tools'))
spec=importlib.util.spec_from_file_location('reviewed_update_catalog',repo/'tools/update_catalog.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
generated={}
def capture_write(path,data,*args,**kwargs):
    f=str(path.relative_to(repo));generated[f]=sha(data.encode());check('independent regeneration exact '+f,data.encode()==path.read_bytes());return len(data)
with patch.object(Path,'write_text',capture_write),patch.object(sys,'argv',['update_catalog.py','--base-ref',incoming]):mod.main()
check('generator writes captured without source mutation',len(generated)==13)
check('ID validator passed','Validated 217 permanent problem IDs against origin/main' in (scratch/'ids.log').read_text())
tests=(scratch/'id-tests.log').read_text();check('17 permanent ID tests passed','Ran 17 tests' in tests and '\nOK\n' in tests)
gitdiff=git('diff',incoming,commit,'--',*sorted(index));(scratch/'index-diff.patch').write_bytes(gitdiff)
report={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent non-implementing AI','phase':'publication integration supplement only','result':'PASS','commit':commit,'parents':[publication,incoming],'tree':git('rev-parse',commit+'^{tree}').decode().strip(),'checks_count':len(checks),'checks':[x for x in checks if not x.startswith('incoming preserved ')],'incoming_all_path_preservation_checks':sum(x.startswith('incoming preserved ') for x in checks),'incoming_full_tree_sha256':sha(json.dumps(main,sort_keys=True).encode()),'all_121_PF02_sha256':protected,'incoming_paths_total':len(incoming_changes),'incoming_paths_exact':len(incoming_changes)-len(adjusted),'incoming_paths_adjusted_for_PF02_totals':adjusted,'incoming_change_git_metadata':{f:main[f] for f in incoming_changes},'status_counts':dict(counts),'generated_sha256':generated,'commands':[{'command':'python3 tools/validate_problem_ids.py --base-ref origin/main','exit':0},{'command':"python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v",'exit':0},{'command':'tools/update_catalog.py main with --base-ref d8c38a79 and Path.write_text intercepted for read-only exact comparison','exit':0}],'no_new_Linux_or_Comparator_execution':True,'historical_source_operational_publication_reviews_unchanged':True}
(scratch/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'result':'PASS','checks':len(checks),'incoming_exact':len(incoming_changes)-len(adjusted),'incoming_adjusted':adjusted,'generated_files':len(generated),'audit_sha256':sha((scratch/'audit.json').read_bytes())}))
