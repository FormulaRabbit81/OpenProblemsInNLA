"""Root's independent review of the accepted KE-05 publication transition."""
from pathlib import Path
import datetime, hashlib, io, json, re, subprocess, zipfile
B=Path('/tmp/nla-lean-next-20260915'); W=Path('/private/tmp/nla-lean-next-ke05-worktree')
REL='randomized-and-low-rank-approximation/KE-05/lean'; P=W/REL
HEAD='414371c9a76aafd7477d9705f9644f7efeb5e329'
O=P/'verification/publication-2026-09-16/root-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def git(*args):return subprocess.check_output(['git','-c','gc.auto=0',*args],cwd=W)
assert not O.exists()
assert sha(B/'KE05-PUBLICATION-PREPARED.json')=='8af701a1ff94e268b1f0f0d85fc386f5222d71e6203415af28da9f51f9c433d6'
a=read(B/'KE05-PUBLICATION-PREPARED.json'); assert a['HEAD']==HEAD
assert git('rev-parse','HEAD').decode().strip()==HEAD
assert len(a['project_files'])==214 and len(a['tracked_modified_files'])==10
for rel,v in a['project_files'].items():assert sha(P/rel)==v['sha256'],rel
for rel,v in a['tracked_modified_files'].items():assert sha(W/rel)==v['sha256'],rel
assert set(git('diff','--name-only').decode().splitlines())==set(a['tracked_modified_files'])
transition=read(P/'verification/publication-2026-09-16/TRANSITION.json')
old=transition['all151_accepted_inputs'];assert len(old)==151
changed=[]
for rel,h in old.items():
    assert hashlib.sha256(git('show',HEAD+':'+REL+'/'+rel)).hexdigest()==h,rel
    if sha(P/rel)!=h:changed.append(rel)
assert set(changed)=={'README.md','formalization.yaml'}
math=[rel for rel in old if rel.endswith('.lean')
      and (rel.startswith('NLA/') or rel in {'Solution.lean','Challenge.lean'})]
assert len(math)==23 and all(sha(P/rel)==old[rel] for rel in math)
before=git('show',HEAD+':randomized-and-low-rank-approximation/KE-05/README.md').decode()
current=(P.parent/'README.md').read_text();marker='## Original statement (retained)'
assert before[before.index(marker):]==current[current.index(marker):]
for rel,h in transition['retained_original_manuscripts'].items():
    assert sha(W/rel)==hashlib.sha256(git('show',HEAD+':'+rel)).hexdigest()==h,rel
assert (W/'problem_ids.json').read_bytes()==git('show',HEAD+':problem_ids.json')
assert len(read(W/'problem_ids.json'))==217
checks=P/'verification/publication-2026-09-16/checks'
assert sha(checks/'CHECKS.json')=='3497b52dcf24dc31ebbe95f50959f1109a8213b32a8ecf8929b375d35a49934c'
assert sha(checks/'MANIFEST.json')=='44ac6f90798ee4a5eef15472d5e4beb2684f39c9244f2336a9c1a3bd5e042875'
for rel,h in read(checks/'MANIFEST.json')['files'].items():assert sha(checks/rel)==h,rel
copied=read(checks/'COPIED-EVIDENCE-AND-REFEREE-BINDINGS.json');assert len(copied)==30
original=B/'canonical-runs/KE05-35058392398'
for row in copied:
    rel=row['path'];assert sha(P/rel)==row['sha256'],rel
    prefix='verification/linux-2026-09-16/'
    if rel.startswith(prefix):assert (P/rel).read_bytes()==(original/rel[len(prefix):]).read_bytes(),rel
rx=re.compile(rb'[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
scanned=[]
for rel in a['project_files']:
    if rel in old and rel not in changed:continue
    f=P/rel
    if f.suffix=='.zip':
        with zipfile.ZipFile(f) as z:
            for n in z.namelist():assert not rx.search(z.read(n)),(rel,n)
    elif f.suffix!='.pdf':assert not rx.search(f.read_bytes()),rel
    scanned.append(rel)
pdf=P.parent/'problem.pdf';assert sha(pdf)=='8c2088e1d476380508cc63845752c29b25bc9f027a07e7969f5965f8c3234f3e'
pdftext=subprocess.check_output(['pdftotext',str(pdf),'-']);assert not rx.search(pdftext)
assert b'Sidney Holden' in pdftext and b'George Stepaniants' in pdftext
pages={str(n):sha(B/f'tmp/pdfs/ke05-publication/page-{n}.png') for n in range(1,5)}
assert subprocess.run(['git','diff','--check'],cwd=W,capture_output=True).returncode==0
O.mkdir()
(O/'REVIEW.md').write_text('''# KE-05 independent root publication review

Approve the exact prepared publication package for commit and a fresh published-head Linux run. Root independently reviewed all changed canonical/Lean documentation, formalization metadata, generated index/RESOLVED changes and the small KE-05-only renderer change. I visually inspected all four rendered PDF pages: mathematical displays, credits, verification evidence, retained original statement, references and history are legible and unclipped. No document correction was needed.

All 214 prepared project files and ten tracked modifications match the preparer's sealed candidate. Independently comparing all 151 previous inputs against the actual accepted Git commit leaves precisely README.md and formalization.yaml changed. All 23 mathematical Lean files, Challenge, frozen records, pins, checker settings and the accepted Solution default are unchanged. The complete original canonical statement from its retained heading onward and all three solution files remain exact. The 217-entry permanent-ID registry is unchanged. Generated counts are branch-local, not the campaign-wide completion count.

Sidney Holden retains authorship and Apache-2.0 credit for the reused formalization. George Stepaniants retains mathematical and integration/verification credit with the Department of Computing and Mathematical Sciences, California Institute of Technology. Nian Shao retains original framework and conjecture credit. New public text and ZIP payloads were independently scanned for contact addresses; the updated PDF text contains no email. The two existing complete-source mathematical reviews remain the mathematical fidelity evidence; this is an independent publication review, not a claim that root reread every mathematical proof file again.

The accepted literal proof commit is 414371c9a76aafd7477d9705f9644f7efeb5e329, actual canonical Linux run 35058392398. Root previously read the entire independent fresh-runtime review and checked its sealed bindings. The current publication copies match the retained actual evidence. Its actual executor and the audit helper's fixed root label are explicitly distinguished. All ten exports, actual LeanCert kernel-trust assertions, Comparator, default-kernel replay, standard transitive axioms and required project controls are supported by that execution. The cancelled initial all-project run is not used as acceptance. The exact algebra and measure argument require no interval search.

The preparer executed schema validation, the required permanent-ID validator before catalog generation, all 17 ID tests, mathematical formatting and PDF generation. Their sealed command/check records were checked; root did not repeat unchanged successful tests. This review used only static Python/Git/PDF inspection, no local Lean/Lake/cache. It changes no mathematical source. A fresh check of the later publication commit and an upstream PR to main are still required; this review does not claim those have already happened or increase the accepted count.
''')
record={'reviewer':'/root','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'verdict':'approve publication; new literal-head run and upstream submission pending',
        'candidate_sha256':sha(B/'KE05-PUBLICATION-PREPARED.json'),'all214_project_files_bound':True,
        'all10_tracked_changes_bound':True,'accepted_proof_commit':HEAD,'proof_run':35058392398,
        'all151_previous_Git_inputs_compared':True,'changed_prior_inputs':changed,
        'unchanged_math_sources':{r:old[r] for r in math},'original_target_and_manuscripts_unchanged':True,
        'ID_registry_unchanged':217,'preparer_checks_manifest_sha256':sha(checks/'MANIFEST.json'),
        'copied_evidence_bindings':copied,'new_or_changed_project_files_privacy_scanned':scanned,
        'PDF_sha256':sha(pdf),'all_four_pages_visually_inspected':True,'page_PNG_sha256':pages,
        'local_Lean_Lake_cache':False,'new_published_commit_run':False,'count_changed':False}
dump(O/'CHECKS.json',record);(O/'review_publication.py').write_bytes(Path(__file__).read_bytes())
dump(O/'MANIFEST.json',{'files':{p.name:sha(p) for p in sorted(O.iterdir()) if p.is_file()}})
final=dict(a);final['kind']='KE05 root-approved publication candidate; literal-head execution pending'
final['root_review_sha256']=sha(O/'REVIEW.md');final['root_manifest_sha256']=sha(O/'MANIFEST.json')
final['project_files']={str(p.relative_to(P)):{'sha256':sha(p),'bytes':p.stat().st_size}
                        for p in sorted(P.rglob('*')) if p.is_file()}
assert len(final['project_files'])==218
final['project_file_count']=218;final['new_project_files']=67
final['project_bytes']=sum(x['bytes'] for x in final['project_files'].values())
final['pending']='commit/push, literal published-head execution, upstream PR and upstream execution'
dump(B/'KE05-ROOT-APPROVED-PUBLICATION.json',final)
print(json.dumps({'root_review_sha256':sha(O/'REVIEW.md'),'root_manifest_sha256':sha(O/'MANIFEST.json'),
                  'final_candidate_sha256':sha(B/'KE05-ROOT-APPROVED-PUBLICATION.json'),
                  'project_files':len(final['project_files'])},indent=2))
