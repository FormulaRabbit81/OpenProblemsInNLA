from pathlib import Path
import ast,collections,hashlib,importlib.util,json,re,subprocess,sys,zipfile
from unittest.mock import patch
import yaml
repo=Path('/private/tmp/nla-formalization-sp04-20260915')
scratch=Path(__file__).parent
prefix='eigenvalues-and-inverse-problems/SP-04/'
project=repo/prefix/'lean'
proof='fcd722e923a339dfeee89051886e82c7384a04d7'
base='d8c38a795876b132c90df8d1be8682d3dcde394c'
checks=[]
def ck(n,c):assert c,n;checks.append(n)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
def data(p):return (repo/p).read_bytes()
def seal(path):
    results={}
    for line in path.read_text().splitlines():
        h,name=line.split(None,1);name=name.lstrip('*');ck('sealed '+str(path.parent/name),sha((path.parent/name).read_bytes())==h);results[name]=h
    return results
ck('proof HEAD exact',git('rev-parse','HEAD').decode().strip()==proof)
ck('base exact',git('rev-parse','origin/main').decode().strip()==base)
changed=git('diff','--name-only').decode().splitlines()
expected={'README.md','CATALOG.md','eigenvalues-and-inverse-problems/README.md',prefix+'README.md',prefix+'lean/README.md',prefix+'lean/formalization.yaml',prefix+'problem.pdf',prefix+'problem.tex','tools/render_problems.py'}
ck('exact nine modified tracked publication files',set(changed)==expected)
all_base_changes=git('diff','--name-only',base,'--').decode().splitlines()
ck('all existing verification files and unrelated published files preserved',all(f.startswith(prefix) or f in {'README.md','CATALOG.md','eigenvalues-and-inverse-problems/README.md','tools/render_problems.py'} for f in all_base_changes))
raw=data(prefix+'README.md').decode()
recovered,n=re.subn(r'<!-- lean-verification -->.*?<!-- /lean-verification -->\n\n','',raw,flags=re.S)
ck('single inserted verification notice',n==1)
recovered=recovered.replace('**Status:** Lean verified','**Status:** Solved').replace('**Last checked:** 2026-09-15','**Last checked:** 2026-09-11')
ck('canonical exact recovery against published main',recovered.encode()==git('show',base+':'+prefix+'README.md'))
ck('canonical exact recovery against proof revision',recovered.encode()==git('show',proof+':'+prefix+'README.md'))
original_sha=sha(recovered.encode())
registry=json.loads(data('problem_ids.json'));ck('217 permanent IDs and unchanged registry',len(registry)==217 and data('problem_ids.json')==git('show',base+':problem_ids.json'))
counts=collections.Counter()
for ident,f in registry.items():
    b=data(f);counts[re.search(r'^\*\*Status:\*\*\s+(.+?)\s*$',b.decode(),re.M).group(1)]+=1
    if ident!='SP-04':ck('other canonical unchanged '+ident,b==git('show',base+':'+f))
ck('exact status totals',dict(counts)=={'Lean verified':35,'Solved':69,'Open':42,'Partially resolved':71})
for f in [prefix+'solution.md',prefix+'solution.tex','references/colbrook-2026-09-11/verification/reviews/SP-04-review.md']:
    ck('original complete source preserved '+f,data(f)==git('show',base+':'+f)==git('show',proof+':'+f))
final=json.loads((project/'reviews/final-source-inputs.json').read_text())['input_sha256']
freeze=json.loads((project/'reviews/statement-inputs.json').read_text())['input_sha256']
for f,h in freeze.items():ck('frozen input '+f,sha((project/f).read_bytes())==h)
final_changed=[f for f,h in final.items() if sha((project/f).read_bytes())!=h]
ck('24/26 final source inputs unchanged; only two publication documents updated',set(final_changed)=={'README.md','formalization.yaml'} and len(final)==26)
archive=project/'verification/linux-2026-09-15'
archive_hashes=seal(archive/'SHA256SUMS');ck('17 raw archive/provenance hashes',len(archive_hashes)==17)
zip_path=archive/'lean-SP-04.zip'
ck('authenticated original ZIP hash unchanged',sha(zip_path.read_bytes())=='eae47bb19e2a64ffc99e383b204c8be89136cfe5755deb86f1e49981c9d1aa6a')
with zipfile.ZipFile(zip_path) as z:
    names=[i.filename for i in z.infolist() if not i.is_dir()];ck('13 unique ZIP members',len(names)==len(set(names))==13)
    for name in names:ck('ZIP member '+name,z.read(name)==(archive/name).read_bytes())
receipt=json.loads((archive/'verify-20260915T213139Z-3935/result.json').read_text())
ck('receipt exact proof revision',receipt['repository_commit']==proof)
inputs=receipt['input_sha256'];ck('88 receipt inputs',len(inputs)==88)
receipt_changed=[]
for f,h in inputs.items():
    ck('receipt input immutable Git '+f,sha(git('show',proof+':'+prefix+'lean/'+f))==h)
    if sha((project/f).read_bytes())!=h:receipt_changed.append(f)
ck('86/88 receipt inputs remain current; exactly two publication docs changed',set(receipt_changed)=={'README.md','formalization.yaml'})
reviews={}
for name in ['statement-referee-1','statement-referee-2','final-referee-1','final-referee-2','linux-referee-1','linux-referee-2']:
    f=project/'reviews'/f'{name}.md';reviews[f.name]=sha(f.read_bytes())
    ck('review exists and approves '+name,any(x in f.read_text() for x in ['PASS','APPROVE']))
    checksum=project/'reviews'/f'{name}-evidence'/'SHA256SUMS'
    if checksum.exists():seal(checksum)
    else:
        for f in (project/'reviews'/f'{name}-evidence').rglob('*'):
            if f.is_file():ck('review evidence exact proof Git '+str(f.relative_to(project)),f.read_bytes()==git('show',proof+':'+str(f.relative_to(repo))))
ck('own operational review seal unchanged',reviews['linux-referee-1.md']=='ae294454043517fa0f8952ce8b5cfa3cf2b55761d0bac5f79d3b433a0b8c35bc')
for f in ['tools/lean/source-lock.json','tools/lean/harness.py','.github/workflows/lean-verification.yml']:
    ck('shared checker unchanged '+f,data(f)==git('show',proof+':'+f)==git('show',base+':'+f))
metadata=yaml.safe_load((project/'formalization.yaml').read_text())
ck('11 metadata exports exact receipt',len(metadata['status']['main_results'])==11 and [x['declaration'] for x in metadata['status']['main_results']]==receipt['config']['theorem_names'])
ck('permitted axioms unchanged',metadata['status']['axioms']==receipt['config']['permitted_axioms'])
ck('formalization author requested',metadata['project']['authors']==['George Stepaniants'])
ck('full requested affiliation',metadata['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology')
for f in [prefix+'README.md',prefix+'lean/README.md',prefix+'lean/formalization.yaml']:
    text=data(f).decode();old=git('show',proof+':'+f).decode()
    ck('no new contact email '+f,set(re.findall(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',text))<=set(re.findall(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',old)))
    ck('Colbrook attribution retained '+f,'Matthew J. Colbrook' in text)
    ck('run cited '+f,'35025876241' in text)
ck('metadata full proof revision and artifact SHA',proof in (project/'formalization.yaml').read_text() and 'eae47bb19e2a64ffc99e383b204c8be89136cfe5755deb86f1e49981c9d1aa6a' in (project/'formalization.yaml').read_text())
indexes=['README.md','CATALOG.md','eigenvalues-and-inverse-problems/README.md']
for f in indexes:
    text=git('show',base+':'+f).decode().replace('70 solved (published or independently audited); 34 solved with Lean verification.','69 solved (published or independently audited); 35 solved with Lean verification.')
    text=''.join(line.replace('**✅ SOLVED**','**🏆 LEAN VERIFIED**') if line.startswith('| [SP-04](') else line for line in text.splitlines(keepends=True))
    ck('only exact intended index update '+f,text.encode()==data(f))
sys.path.insert(0,str(repo/'tools'))
spec=importlib.util.spec_from_file_location('review_catalog',repo/'tools/update_catalog.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
generated={}
def capture_write(path,content,*args,**kwargs):
    f=str(path.relative_to(repo));generated[f]=sha(content.encode());ck('readonly regenerated index exact '+f,content.encode()==path.read_bytes());return len(content)
with patch.object(Path,'write_text',capture_write),patch.object(sys,'argv',['update_catalog.py','--base-ref',base]):mod.main()
ck('13 generated files compared without mutation',len(generated)==13)
def restore_function(source):
    fn=next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef) and n.name=='restore_pdf_layout');scope={};exec(compile(ast.Module(body=[fn],type_ignores=[]),'review-function','exec'),scope);return scope['restore_pdf_layout']
class RemoveSP04(ast.NodeTransformer):
    def visit_If(self,node):
        if ast.unparse(node.test)=="identifier == 'SP-04'":return None
        return self.generic_visit(node)
original_ast=ast.parse(git('show',proof+':tools/render_problems.py').decode())
modified_ast=RemoveSP04().visit(ast.parse(data('tools/render_problems.py').decode()))
ck('renderer only two narrow SP04 branches; other AST unchanged',ast.dump(original_ast)==ast.dump(modified_ast))
old_restore=restore_function(git('show',proof+':tools/render_problems.py').decode());new_restore=restore_function(data('tools/render_problems.py').decode())
for ident,f in registry.items():
    body=data(f).decode()
    if ident!='SP-04':ck('layout unchanged for '+ident,old_restore(ident,body)==new_restore(ident,body))
    else:ck('only one SP04 pagebreak in body',new_restore(ident,body)==old_restore(ident,body).replace('## Original problem statement\n','\\newpage\n\n## Original problem statement\n',1))
text=(scratch/'pdf-text.txt').read_text();pages=text.split('\f');ck('exact three PDF pages',len([x for x in pages if x.strip()])==3)
ck('full original question located page two','Original problem statement' in pages[1] and 'one-to-one to stationary matrices' in pages[1] and 'hold for every' in pages[1])
ck('truthful verification footer corrected across all PDF pages',text.count('Verification check: 2026-09-15')==3 and 'Literature check:' not in text)
ck('exact final PDF hash',sha(data(prefix+'problem.pdf'))=='054fec6d28edf9813a792eb522be249f2794490a35df5bcb3f24ad39c4917b53')
ck('original attribution and requested author in PDF',all(x in pages[0] for x in ['George Stepaniants','Matthew J. Colbrook','California']))
ck('IDs validator pass','Validated 217 permanent problem IDs against origin/main' in (scratch/'ids.log').read_text())
ck('17 ID tests pass','Ran 17 tests' in (scratch/'id-tests.log').read_text() and '\nOK\n' in (scratch/'id-tests.log').read_text())
ck('metadata11 coverage pass','PASS (11 declarations)' in (scratch/'metadata.log').read_text())
ck('whitespace check with intentional Markdown hard breaks allowed passed',(scratch/'diff-check.log').read_bytes()==b'')
result={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review; independent non-implementing AI','phase':'SP-04 publication supplement','result':'PASS for machine checks; visual and prose assessment separately recorded in report','proof_commit':proof,'published_base':base,'checks_count':len(checks),'checks':checks,'publication_sha256':{f:sha(data(f)) for f in sorted(expected)},'recovered_canonical_sha256':original_sha,'status_counts':dict(counts),'freeze_inputs':freeze,'final_source_inputs_unchanged':{f:h for f,h in final.items() if f not in final_changed},'receipt_changed_publication_docs':receipt_changed,'review_sha256':reviews,'archive_sha256sums_sha256':sha((archive/'SHA256SUMS').read_bytes()),'generated_index_sha256':generated,'pdf_pages_independently_rendered_and_visually_inspected':3,'fresh_Linux_or_Comparator_execution':False}
(scratch/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
(scratch/'publication-diff.patch').write_bytes(git('diff','--',*sorted(expected- {prefix+'problem.pdf'})))
print(json.dumps({'checks':len(checks),'result':'PASS','publication_sha256':result['publication_sha256']}))
