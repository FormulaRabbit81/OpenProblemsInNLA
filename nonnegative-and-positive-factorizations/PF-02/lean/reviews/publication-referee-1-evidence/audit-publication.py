from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess,zipfile

repo=Path('/private/tmp/nla-formalization-pf02-20260915')
project=repo/'nonnegative-and-positive-factorizations/PF-02/lean'
scratch=Path(__file__).resolve().parent
archive=project/'verification/linux-2026-09-15'
raw=archive/'verify-20260915T204142Z-4353'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
git=lambda *args:subprocess.check_output(['git',*args],cwd=repo)
checks=[]
def check(label,value):
    assert value,label
    checks.append(label)
base=git('rev-parse','origin/main').decode().strip()
proof='a3e984ced348f4d8529c5d0f8f87c9be7dd979e2'
check('expected published base',base=='8f04b905eb2e0827b6b84f37d9d080ae1f05b202')
check('publication edits based on verified proof commit',git('rev-parse','HEAD').decode().strip()==proof)
canonical='nonnegative-and-positive-factorizations/PF-02/README.md'
old=git('show',f'{base}:{canonical}').decode()
new=(repo/canonical).read_text()
notice=re.search(r'\n<!-- lean-verification -->\n.*?<!-- /lean-verification -->\n',new,re.S)
check('one new bounded verification notice',notice is not None and new.count('<!-- lean-verification -->')==1)
recovered=new[:notice.start()]+new[notice.end():]
recovered=recovered.replace('**Status:** Lean verified  \n','**Status:** Solved  \n',1)
recovered=recovered.replace('**Last checked:** 2026-09-15  \n','**Last checked:** 2026-09-11  \n',1)
check('whole canonical page exactly recovered after status/date/notice removal',recovered==old)
check('canonical page preserved original full mathematical statement',new[new.index('## Context and notation'):]==old[old.index('## Context and notation'):])
registry=load(repo/'problem_ids.json')
check('all 217 registry IDs unchanged',len(registry)==217 and (repo/'problem_ids.json').read_bytes()==git('show',f'{base}:problem_ids.json'))
for identifier,path in registry.items():
    if identifier!='PF-02':check('other canonical unchanged '+identifier,(repo/path).read_bytes()==git('show',f'{base}:{path}'))
counts=Counter(re.search(r'^\*\*Status:\*\* (.*?)\s*$',(repo/path).read_text(),re.M)[1] for path in registry.values())
check('expected exact branch catalog counts',counts=={'Lean verified':32,'Solved':72,'Open':42,'Partially resolved':71})
for path in ['README.md','CATALOG.md','nonnegative-and-positive-factorizations/README.md']:
    before=git('show',f'{base}:{path}').decode()
    expected=before.replace('**Resolution evidence:** 73 solved (published or independently audited); 31 solved with Lean verification.',
                            '**Resolution evidence:** 72 solved (published or independently audited); 32 solved with Lean verification.')
    lines=expected.splitlines(keepends=True)
    expected=''.join(line.replace('**✅ SOLVED**','**🏆 LEAN VERIFIED**') if line.startswith('| [PF-02](') else line for line in lines)
    check('catalog exact expected change '+path,(repo/path).read_text()==expected)
frozen=load(project/'reviews/statement-freeze.json')['input_sha256']
for name,want in frozen.items():check('frozen boundary unchanged '+name,sha(project/name)==want)
check('ten pre-proof inputs checked',len(frozen)==10)
full=load(project/'reviews/final-source-inputs.json')['input_sha256']
publication_docs={'README.md','formalization.yaml'}
for name,want in full.items():
    if name not in publication_docs:check('approved non-publication source unchanged '+name,sha(project/name)==want)
check('eighteen non-publication final inputs checked',len(set(full)-publication_docs)==18)
receipt=load(raw/'result.json');changed_receipt=[]
for name,want in receipt['input_sha256'].items():
    if sha(project/name)!=want:changed_receipt.append(name)
check('only two publication documents differ from all 70 receipt inputs',set(changed_receipt)==publication_docs and len(receipt['input_sha256'])==70)
check('exact verified proof revision retained',receipt['repository_commit']==proof)
check('run artifact digest retained',sha(archive/'lean-PF-02.zip')=='a62edf32bfdf4ef70abcabe572ca8fffb6ba2b0d2f4f6ddc879df99229ffb6c9')
for line in (archive/'SHA256SUMS').read_text().splitlines():
    want,name=line.split('  ',1);check('raw archive unchanged '+name,sha(archive/name)==want)
with zipfile.ZipFile(archive/'lean-PF-02.zip') as z:
    check('exact extracted authenticated ZIP',all(z.read(n)==(archive/n).read_bytes() for n in z.namelist() if not n.endswith('/')))
context=load(project/'reviews/final-referee-1-evidence/snapshot-inputs.json')['original_source_context_sha256']
for name,want in context.items():
    if name!=canonical:check('original source and attribution unchanged '+name,sha(repo/name)==want)
notice_text=notice.group()+ (project/'README.md').read_text()+ (project/'formalization.yaml').read_text()
check('George name and exact affiliation', 'George Stepaniants' in notice_text and
 'Department of Computing and Mathematical Sciences, California Institute of Technology' in notice_text)
check('no new contact email',not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',notice_text))
for token in ['35021020857','a3e984ced348f4d8529c5d0f8f87c9be7dd979e2','10418540042',
              'a62edf32bfdf4ef70abcabe572ca8fffb6ba2b0d2f4f6ddc879df99229ffb6c9']:
    check('metadata correct provenance '+token,token in (project/'formalization.yaml').read_text() and token in (project/'README.md').read_text())
for name in ['statement-referee-1.md','statement-referee-2.md','final-referee-1.md','final-referee-2.md','linux-referee-1.md','linux-referee-2.md']:
    check('review exists '+name,(project/'reviews'/name).is_file())
check('PDF exactly two pages',bool(re.search(r'^Pages:\s+2$',(scratch/'pdfinfo.txt').read_text(),re.M)))
pdftext=(scratch/'pdf-text.txt').read_text()
for phrase in ['Status: Lean verified','George Stepaniants','Matthew J. Colbrook','Euclidean subspace topology','Give the resulting orbit space the quotient topology.','Problem statement']:
    check('PDF retained text '+phrase,phrase in pdftext)
paths=['CATALOG.md','README.md',canonical,'nonnegative-and-positive-factorizations/PF-02/lean/README.md',
       'nonnegative-and-positive-factorizations/PF-02/lean/formalization.yaml',
       'nonnegative-and-positive-factorizations/PF-02/problem.pdf','nonnegative-and-positive-factorizations/PF-02/problem.tex',
       'nonnegative-and-positive-factorizations/README.md']
check('only expected eight tracked publication files changed',set(git('diff','--name-only').decode().splitlines())==set(paths))
record={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent non-implementing AI',
 'phase':'publication supplement','result':'PASS','published_base':base,'verified_proof_commit':proof,
 'exact_original_canonical_recovery':True,'other_canonical_pages_unchanged':216,'registry_ids':217,
 'catalog_counts':dict(counts),'frozen_inputs_unchanged':10,'non_publication_final_inputs_unchanged':18,
 'receipt_unchanged_inputs':68,'receipt_changed_inputs':changed_receipt,
 'publication_sha256':{n:sha(repo/n) for n in paths},'registry_sha256':sha(repo/'problem_ids.json'),
 'review_sha256':{n:sha(project/'reviews'/n) for n in ['statement-referee-1.md','statement-referee-2.md','final-referee-1.md','final-referee-2.md','linux-referee-1.md','linux-referee-2.md']},
 'pdf':{'pages':2,'bytes':(repo/'nonnegative-and-positive-factorizations/PF-02/problem.pdf').stat().st_size,
        'independently_rendered_and_visually_inspected_pages':[1,2],'visual_result':'Both clean: no clipping, missing glyphs or overlaps; all mathematical target and attribution text present.'},
 'checks_count':len(checks),'checks':checks}
(scratch/'audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['result','checks_count','catalog_counts','receipt_unchanged_inputs','receipt_changed_inputs','publication_sha256']},indent=2))
