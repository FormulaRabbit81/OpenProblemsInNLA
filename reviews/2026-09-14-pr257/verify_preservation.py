#!/usr/bin/env python3
"""Read-only integration preservation receipt; use after final content commit."""
import argparse,json,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument('--repo',default='.'); p.add_argument('--ref',default='HEAD'); p.add_argument('--out'); a=p.parse_args()
repo=Path(a.repo); base='01866d4589bc1df4144f7686fba0ba58947f7b0b'; source='65e53895c41d415fa560628f577d4de264eb2522'
def git(*args): return subprocess.check_output(['git','-C',str(repo),*args])
def content(ref,path): return git('show',ref+':'+path)
head=git('rev-parse',a.ref).decode().strip()
registry=json.loads(content(base,'problem_ids.json'))
assert content(base,'problem_ids.json')==content(head,'problem_ids.json')
changed=git('diff','--name-only',base,head).decode().splitlines()
allowed={'README.md','CATALOG.md','RESOLVED.md','matrix-inequalities-and-norms/README.md','matrix-inequalities-and-norms/MI-32/README.md','matrix-inequalities-and-norms/MI-32/problem.tex','matrix-inequalities-and-norms/MI-32/problem.pdf'}
assert all(n in allowed or n.startswith('reviews/2026-09-14-pr257/') for n in changed)
before_paths=set(git('ls-tree','-r','--name-only',base).decode().splitlines()); after_paths=set(git('ls-tree','-r','--name-only',head).decode().splitlines())
assert before_paths<=after_paths
counts={}
for id,path in registry.items():
 before=content(base,path); after=content(head,path)
 oldstat=re.search(rb'^\*\*Status:\*\* (.*?)\s*$',before,re.M).group(1).decode()
 stat=re.search(rb'^\*\*Status:\*\* (.*?)\s*$',after,re.M).group(1).decode(); counts[stat]=counts.get(stat,0)+1
 if id!='MI-32': assert before==after,id
 else:
  assert oldstat=='Partially resolved' and stat=='Lean verified'
  for field in ['Difficulty','Importance','Rating rationale']:
   exp=rb'^\*\*'+field.encode()+rb':\*\*.*$'; assert re.search(exp,before,re.M).group()==re.search(exp,after,re.M).group()
  # All original named sections survive verbatim; the new evidence is inserted before Known cases.
  for block in re.split(rb'(?m)(?=^## )',before)[1:]: assert block.strip() in after,block[:60]
  assert b'M(X)=\\sqrt n>0' not in after and b'M(X)>0' in after
  assert b'whole local Lean gate' in after
  assert b'../../reviews/2026-09-14-pr257/README.md' in after
for ref in [base,source]:
 original=content(ref,'RESOLVED.md').decode(); actual=content(head,'RESOLVED.md').decode()
 for block in re.split(r'(?m)(?=^### )',original): assert block.strip() in actual,block[:60]
assert counts=={'Open':42,'Partially resolved':72,'Solved':72,'Lean verified':31},counts
for ancestor in [base,source,'cc661b4170e590daeb2ca4232336ab8b6d2eeaaf']: subprocess.run(['git','-C',str(repo),'merge-base','--is-ancestor',ancestor,head],check=True)
result={'status':'PASS','published_base':base,'source_pr':257,'source_head':source,'reviewed_ref':head,'tree':git('rev-parse',head+'^{tree}').decode().strip(),'base_paths_retained':len(before_paths),'permanent_ids':len(registry),'other_canonical_pages_byte_unchanged':216,'MI32_all_original_sections_and_ratings_retained':True,'both_resolution_histories_retained':True,'source_head_ancestor':True,'only_changed_target':'MI-32','status_counts':counts,'original_seven_path_scope_preserved':True,'no_lean_or_workflow_or_safeguard_changes':True}
s=json.dumps(result,indent=2)+'\n'
if a.out: Path(a.out).write_text(s)
print(s)
