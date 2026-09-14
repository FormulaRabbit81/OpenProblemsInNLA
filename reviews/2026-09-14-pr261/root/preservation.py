#!/usr/bin/env python3
import subprocess,json,hashlib,re,argparse
from pathlib import Path
from pypdf import PdfReader
parser=argparse.ArgumentParser(); parser.add_argument('--repo',type=Path,default=Path('/private/tmp/nla-audit-261')); parser.add_argument('--out',type=Path,default=Path('/private/tmp/nla-review-261/preservation.json')); args=parser.parse_args()
root=args.repo; ref='9bf50028bc30e6cdf78e19089befcb9b9bd6c292'; base='27540c8022a33fef171625b7e48a95e33562d535'
def git(*args): return subprocess.check_output(['git','-C',str(root),*args])
def tree(rev):
 return {line.split(b'\t',1)[1].decode():line.split(b'\t',1)[0].decode() for line in git('ls-tree','-rz',rev).split(b'\0') if line}
def read(rev,path):return git('show',rev+':'+path)
btree,ftree=tree(base),tree(ref); added=set(ftree)-set(btree); changed={p for p in btree if ftree.get(p)!=btree[p]}
assert not set(btree)-set(ftree)
allowed={'RESOLVED.md'}|{f'arithmetic-and-complexity/AC-{n:02d}/{f}' for n in range(1,7) for f in ['README.md','problem.tex','problem.pdf']}
assert changed==allowed,changed
assert all(p.startswith('references/holden-ac-2026-09-14/') for p in added)
reg=json.loads(read(base,'problem_ids.json')); assert read(base,'problem_ids.json')==read(ref,'problem_ids.json')
for id,path in reg.items():
 a=read(base,path); b=read(ref,path)
 if id in [f'AC-{n:02d}' for n in range(1,7)]:
  assert b.split(b'\n## Reviewed research submission')[0].replace(b'**Last checked:** 2026-09-14',b'**Last checked:** 2026-09-10').rstrip()==a.rstrip(),id
 else: assert a==b,id
original=read(base,'RESOLVED.md'); new=read(ref,'RESOLVED.md'); start=b'## Reviewed AC-01'; end=b'## Resolved catalog entries'
i=new.index(start); j=new.index(end,i)
assert new[:i]+new[j:]==original
pkg=root/'references/holden-ac-2026-09-14'; prov=json.loads((pkg/'provenance.json').read_text()); listed={}
for archive,info in prov.items():
 for path,digest in info['files'].items():
  assert path not in listed,path
  listed[path]=digest
  assert hashlib.sha256((pkg/'submitted'/path).read_bytes()).hexdigest()==digest,path
actual={str(p.relative_to(pkg/'submitted')) for p in (pkg/'submitted').rglob('*') if p.is_file()}
assert actual==set(listed),(actual-set(listed),set(listed)-actual)
reports={'AC-01':'AC01_round3_research_pack/report/AC01_round3_report.pdf','AC-02':'AC02_updated_research_pack/round2/report/AC02_continuation.pdf','AC-03':'AC03_updated_pack/AC03_round3_verified/report.pdf','AC-04':'AC04_symmetric_extraction/report.pdf','AC-05':'AC05_power_rigidity/report/AC05_power_rigidity.pdf','AC-06':'AC06_round4/report.pdf'}
report_records={}
for id,path in reports.items():
 src=PdfReader(pkg/'submitted'/path); out=PdfReader(pkg/(id+'-submission.pdf'))
 assert len(out.pages)==len(src.pages)+1
 for i,p in enumerate(src.pages):
  q=out.pages[i+1]
  assert p.get_contents().get_data()==q.get_contents().get_data(),(id,i)
  assert list(p.mediabox)==list(q.mediabox) and list(p.cropbox)==list(q.cropbox),(id,i)
  assert p.extract_text()==q.extract_text(),(id,i)
 assert 'Sidney Holden' in out.pages[0].extract_text()
 report_records[id]={'original_pages':len(src.pages),'cover_pages':1,'all_original_page_streams_boxes_text_unchanged':True,'original_sha256':hashlib.sha256((pkg/'submitted'/path).read_bytes()).hexdigest(),'attributed_sha256':hashlib.sha256((pkg/(id+'-submission.pdf')).read_bytes()).hexdigest()}
result={'status':'PASS','base':base,'source_head':ref,'source_tree':git('rev-parse',ref+'^{tree}').decode().strip(),'base_paths_retained':len(btree),'modified_existing_paths':len(changed),'new_reference_paths':len(added),'registered_ids_unchanged':len(reg),'original_targets_ratings_statuses_and_prior_text_unchanged':True,'all_prior_resolved_text_retained':True,'all_indexes_unchanged':True,'all_prior_references_unchanged':True,'supplied_members_exact':len(listed),'supplied_member_inventory_exact':True,'source_archive_hashes':'Recorded submission provenance only: original top-level ZIPs are not present, so their container hashes were not independently reauthenticated. Every retained extracted member was freshly hashed.','report_pages':report_records}
args.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
