from pathlib import Path
import ast,collections,hashlib,importlib.util,json,re,subprocess,sys,zipfile
from unittest.mock import patch
import yaml
repo=Path('/private/tmp/nla-formalization-sp05-20260915')
scratch=Path(__file__).parent
prefix='eigenvalues-and-inverse-problems/SP-05/'
project=repo/prefix/'lean'
proof='9c8369dcea69f9f243a0502fb7e89beaa8f49fad'
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
    if ident!='SP-05':ck('other canonical unchanged '+ident,b==git('show',base+':'+f))
ck('exact status totals',dict(counts)=={'Lean verified':35,'Solved':69,'Open':42,'Partially resolved':71})
for f in [prefix+'solution.md',prefix+'solution.tex','references/colbrook-2026-09-11/verification/reviews/SP-05-review.md']:
    ck('original complete source preserved '+f,data(f)==git('show',base+':'+f)==git('show',proof+':'+f))
final=json.loads((project/'reviews/final-source-inputs.json').read_text())['input_sha256']
freeze=json.loads((project/'reviews/statement-inputs.json').read_text())['input_sha256']
for f,h in freeze.items():ck('frozen input '+f,sha((project/f).read_bytes())==h)
final_changed=[f for f,h in final.items() if sha((project/f).read_bytes())!=h]
ck('21/23 final source inputs unchanged; only two publication documents updated',set(final_changed)=={'README.md','formalization.yaml'} and len(final)==23)
archive=project/'verification/linux-2026-09-15'
archive_hashes=seal(archive/'SHA256SUMS');ck('17 raw archive/provenance hashes',len(archive_hashes)==17)
zip_path=archive/'lean-SP-05.zip'
ck('authenticated original ZIP hash unchanged',sha(zip_path.read_bytes())=='bc5c29c91db0be6249c80dbfd3ca0ce2177b58c805b03935d33064bcdb25cdb1')
with zipfile.ZipFile(zip_path) as z:
    names=[i.filename for i in z.infolist() if not i.is_dir()];ck('13 unique ZIP members',len(names)==len(set(names))==13)
    for name in names:ck('ZIP member '+name,z.read(name)==(archive/name).read_bytes())
receipt=json.loads((archive/'verify-20260915T221936Z-4220/result.json').read_text())
ck('receipt exact proof revision',receipt['repository_commit']==proof)
inputs=receipt['input_sha256'];ck('92 receipt inputs',len(inputs)==92)
receipt_changed=[]
for f,h in inputs.items():
    ck('receipt input immutable Git '+f,sha(git('show',proof+':'+prefix+'lean/'+f))==h)
    if sha((project/f).read_bytes())!=h:receipt_changed.append(f)
ck('90/92 receipt inputs remain current; exactly two publication docs changed',set(receipt_changed)=={'README.md','formalization.yaml'})
reviews={}
for name in ['statement-referee-1','statement-referee-2','final-referee-1','final-referee-2','linux-referee-1','linux-referee-2']:
    f=project/'reviews'/f'{name}.md';reviews[f.name]=sha(f.read_bytes())
    ck('review exists and approves '+name,any(x in f.read_text() for x in ['PASS','APPROVE']))
    checksum=project/'reviews'/f'{name}-evidence'/'SHA256SUMS'
    if checksum.exists():seal(checksum)
    else:
        for f in (project/'reviews'/f'{name}-evidence').rglob('*'):
            if f.is_file():ck('review evidence exact proof Git '+str(f.relative_to(project)),f.read_bytes()==git('show',proof+':'+str(f.relative_to(repo))))
ck('own operational review seal unchanged',reviews['linux-referee-1.md']=='da2274d65053c506fbe847668992d56b8626505dc12b1860b91fd1ba8297ef64')
for f in ['tools/lean/source-lock.json','tools/lean/harness.py','.github/workflows/lean-verification.yml']:
    ck('shared checker unchanged '+f,data(f)==git('show',proof+':'+f)==git('show',base+':'+f))
metadata=yaml.safe_load((project/'formalization.yaml').read_text())
ck('6 metadata exports exact receipt',len(metadata['status']['main_results'])==6 and [x['declaration'] for x in metadata['status']['main_results']]==receipt['config']['theorem_names'])
ck('permitted axioms unchanged',metadata['status']['axioms']==receipt['config']['permitted_axioms'])
ck('formalization author requested',metadata['project']['authors']==['George Stepaniants'])
ck('full requested affiliation',metadata['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology')
for f in [prefix+'README.md',prefix+'lean/README.md',prefix+'lean/formalization.yaml']:
    text=data(f).decode();old=git('show',proof+':'+f).decode()
    ck('no new contact email '+f,set(re.findall(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',text))<=set(re.findall(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',old)))
    ck('Colbrook attribution retained '+f,'Matthew J. Colbrook' in text)
    ck('run cited '+f,'35030259545' in text)
ck('metadata full proof revision and artifact SHA',proof in (project/'formalization.yaml').read_text() and 'bc5c29c91db0be6249c80dbfd3ca0ce2177b58c805b03935d33064bcdb25cdb1' in (project/'formalization.yaml').read_text())
indexes=['README.md','CATALOG.md','eigenvalues-and-inverse-problems/README.md']
for f in indexes:
    text=git('show',base+':'+f).decode().replace('70 solved (published or independently audited); 34 solved with Lean verification.','69 solved (published or independently audited); 35 solved with Lean verification.')
    text=''.join(line.replace('**✅ SOLVED**','**🏆 LEAN VERIFIED**') if line.startswith('| [SP-05](') else line for line in text.splitlines(keepends=True))
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
class RemoveSP05(ast.NodeTransformer):
    def visit_If(self,node):
        if ast.unparse(node.test)=="identifier == 'SP-05'":return None
        return self.generic_visit(node)
original_ast=ast.parse(git('show',proof+':tools/render_problems.py').decode())
modified_ast=RemoveSP05().visit(ast.parse(data('tools/render_problems.py').decode()))
ck('renderer only two narrow SP05 branches; other AST unchanged',ast.dump(original_ast)==ast.dump(modified_ast))
old_restore=restore_function(git('show',proof+':tools/render_problems.py').decode());new_restore=restore_function(data('tools/render_problems.py').decode())
for ident,f in registry.items():
    body=data(f).decode()
    if ident!='SP-05':ck('layout unchanged for '+ident,old_restore(ident,body)==new_restore(ident,body))
    else:ck('only one SP05 pagebreak in body',new_restore(ident,body)==old_restore(ident,body).replace('## Problem statement\n','\\newpage\n\n## Problem statement\n',1))
text=(scratch/'pdf-text.txt').read_text();pages=text.split('\f');ck('exact three PDF pages',len([x for x in pages if x.strip()])==3)
ck('full original question located page two','Problem statement' in pages[1] and 'where vec stacks columns' in pages[1] and 'Equivalently, must the smallest eigenvalue' in pages[1])
ck('truthful verification footer corrected across all PDF pages',text.count('Verification check: 2026-09-15')==3 and 'Literature check:' not in text)
ck('exact final PDF hash',sha(data(prefix+'problem.pdf'))=='2475c54bd2a29536eea3192905ce89b0c7fc799db1ce371714f188f9edcdf4f2')
ck('original attribution and requested author in PDF',all(x in re.sub(r'-\s*\n', '', pages[0]) for x in ['George Stepaniants','Matthew J. Colbrook','California']))
ck('IDs validator pass','Validated 217 permanent problem IDs against origin/main' in (scratch/'ids.log').read_text())
ck('17 ID tests pass','Ran 17 tests' in (scratch/'id-tests.log').read_text() and '\nOK\n' in (scratch/'id-tests.log').read_text())
ck('metadata6 coverage pass','PASS (6 declarations)' in (scratch/'metadata.log').read_text())
ck('whitespace check with intentional Markdown hard breaks allowed passed',(scratch/'diff-check.log').read_bytes()==b'')
ck('other operational review seal unchanged',reviews['linux-referee-2.md']=='cbb6558d6a8f1f79b3e3ef3e1c24397266c74ff768f38f42b895be863bc566fb')
ck('ten frozen boundary inputs',len(freeze)==10 and freeze==json.loads((project/'reviews/statement-freeze.json').read_text())['input_sha256'])
ck('full original source PDF unchanged',data(prefix+'solution.pdf')==git('show',base+':'+prefix+'solution.pdf')==git('show',proof+':'+prefix+'solution.pdf'))
ck('actual current canonical promotion',re.search(r'^\*\*Status:\*\* (.+?)\s*$',raw,re.M).group(1)=='Lean verified')
for file in [project/'README.md',repo/prefix/'README.md']:
    for target in re.findall(r'\]\(([^)]+)\)',file.read_text()):
        if not re.match(r'[a-z]+:',target):ck('published local link '+str(file.relative_to(repo))+' '+target,(file.parent/target.split('#')[0]).exists())
ck('PR draft exact mathematical and operational context',all(x in (scratch/'pr-body.md').read_text() for x in ['n≥2','n≥1','George Stepaniants','Department of Computing and Mathematical Sciences, California Institute of Technology',proof,'35030259545','All 92 submitted project inputs','original Colbrook proof','No external human review']))
ck('no new email in PR draft',not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',(scratch/'pr-body.md').read_text()))
current_diagnostics=json.loads((scratch/'optional-exact-check.json').read_text())
ck('documented optional diagnostics succeeds on final publication',current_diagnostics['all_checks_passed'] and current_diagnostics['historical_proof_block_sha256']=='54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42')
for name,want in current_diagnostics['source_sha256'].items():ck('optional diagnostics current source hash '+name,sha(data(name))==want)
result={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review; independent non-implementing AI','phase':'SP-05 publication supplement','result':'PASS for machine checks; visual and prose assessment separately recorded in report','proof_commit':proof,'published_base':base,'checks_count':len(checks),'checks':checks,'publication_sha256':{f:sha(data(f)) for f in sorted(expected)},'recovered_canonical_sha256':original_sha,'status_counts':dict(counts),'freeze_inputs':freeze,'final_source_inputs_unchanged':{f:h for f,h in final.items() if f not in final_changed},'receipt_changed_publication_docs':receipt_changed,'review_sha256':reviews,'archive_sha256sums_sha256':sha((archive/'SHA256SUMS').read_bytes()),'generated_index_sha256':generated,'pdf_pages_independently_rendered_and_visually_inspected':3,'fresh_Linux_or_Comparator_execution':False,'pr_body_sha256':sha((scratch/'pr-body.md').read_bytes()),'optional_diagnostics_sha256':sha((scratch/'optional-exact-check.json').read_bytes())}
(scratch/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
(scratch/'publication-diff.patch').write_bytes(git('diff','--',*sorted(expected- {prefix+'problem.pdf'})))
print(json.dumps({'checks':len(checks),'result':'PASS','publication_sha256':result['publication_sha256']}))
