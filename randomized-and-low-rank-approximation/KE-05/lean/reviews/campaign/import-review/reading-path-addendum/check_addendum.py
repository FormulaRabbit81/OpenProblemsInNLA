"""Read-only audit of the KE-05 142-to-147-file documentation transition."""
from pathlib import Path
import datetime,hashlib,json,re
B=Path('/tmp/nla-lean-next-20260915')
O=B/'reviews/KE05-mf22-import-candidate'
OUT=O/'reading-path-addendum'
P=Path('/private/tmp/nla-lean-next-ke05-worktree/randomized-and-low-rank-approximation/KE-05/lean')
def sha(b):return hashlib.sha256(b).hexdigest()
def digest(p):return sha(p.read_bytes())
def load(p):return json.loads(p.read_text())
old=load(O/'ALL-142-CANDIDATE-INPUTS.json')
manifest=B/'KE05-CAMPAIGN-CANDIDATE.json'
assert digest(manifest)=='b625ea1c0e0f204c4d6af51b112c3e8474314fbe1c1bcd3d4d789fcb6cb9ee53'
new=load(manifest)['files']
assert len(old)==142 and len(new)==147
actual={str(p.relative_to(P)):digest(p) for p in P.rglob('*') if p.is_file()}
assert actual==new
added=sorted(new.keys()-old.keys())
assert added==[
 'reviews/campaign/import-review/CHECKS.json',
 'reviews/campaign/import-review/MANIFEST.json',
 'reviews/campaign/import-review/REVIEW.md',
 'verification/campaign-import-2026-09-16/reading-path-clarification/CHANGE.json',
 'verification/campaign-import-2026-09-16/reading-path-clarification/before-README.md']
assert not old.keys()-new.keys()
assert [p for p in old if old[p]!=new[p]]==['README.md']
v=P/'verification/campaign-import-2026-09-16/reading-path-clarification'
before=(v/'before-README.md').read_bytes()
after=(P/'README.md').read_bytes()
assert sha(before)==old['README.md']
oldphrase=b'For authoritative verification use the shared'
newphrase=b'From the repository root, use the shared'
assert before.count(oldphrase)==1 and before.replace(oldphrase,newphrase,1)==after
assert sha(after)=='84b648e3d1d4f22b3e7b213b3c7650aa4de5ff7d0ebc8c73873d03546050c081'
change=load(v/'CHANGE.json')
assert digest(v/'CHANGE.json')=='3cba35b5c968a7bfa050548b453fda949eeac3346a4db8de21bbe2c38d021a2a'
assert change['before_README_sha256']==sha(before) and change['after_README_sha256']==sha(after)
assert change['independent_review_request_sha256']==digest(O/'REVIEW.md')
assert not change['runtime_claim_changed'] and change['actual_runtime']=='pending'
copied={}
for name in ['REVIEW.md','CHECKS.json','MANIFEST.json']:
 assert (P/'reviews/campaign/import-review'/name).read_bytes()==(O/name).read_bytes()
 copied[name]=digest(O/name)
prior_manifest=load(O/'MANIFEST.json')
for rel,h in prior_manifest['files_sha256'].items():assert digest(O/rel)==h
email=re.compile(rb'[A-Za-z0-9_.+%\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
for rel in added+['README.md']:assert not email.search((P/rel).read_bytes()),rel
checks={'reviewer':'/root/mf22_publication_referee','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'approve exact documentation clarification and five-file evidence addition; fresh runtime acceptance pending',
 'old_candidate_manifest_sha256':'47a08c76ff9ec6398d707db6210b944e60c2d836bb954b55a2bacdf7046a9d79',
 'new_candidate_manifest_sha256':digest(manifest),'all147_current_inputs_verified':True,
 'unchanged_preexisting_files':141,'only_modified_file':'README.md',
 'exact_single_phrase_replacement':True,'new_README_sha256':sha(after),
 'added_files':{rel:new[rel] for rel in added},'copied_review_records_byte_exact':copied,
 'copied_review_scope':'Three selected review/check/manifest records only; their original manifest inventories the full independent packet retained outside the candidate. Do not claim this copied directory is that whole packet.',
 'all_previous_mathematical_config_schema_link_and_attribution_approvals_preserved':True,
 'no_email_matches_in_changed_or_added_files':True,
 'proof_edits_Git_mutations_Lean_execution_or_new_runtime_claim':False}
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print('CHECKS_sha256',digest(OUT/'CHECKS.json'))
