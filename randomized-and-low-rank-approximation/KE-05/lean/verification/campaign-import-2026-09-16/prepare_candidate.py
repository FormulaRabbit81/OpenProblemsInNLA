"""Integrate the existing reviewed KE-05 proof, preserving its authorship and bytes."""
from pathlib import Path
import datetime, hashlib, json, re, shutil, subprocess
import yaml, jsonschema

B=Path('/tmp/nla-lean-next-20260915')
W=Path('/private/tmp/nla-lean-next-ke05-worktree')
P=W/'randomized-and-low-rank-approximation/KE-05/lean'
V=P/'verification/campaign-import-2026-09-16'
SRC='04f3f39beb69d77dbc4a8eadee70259eb89a591a'
TESTED='9acd5d5c9ab91c5c0c07603b6b48c0cb7ede54e6'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def copy(a,b):b.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a,b)

assert not V.exists()
original=read(B/'KE05-IMPORTED-EXACT-SOURCE.json')
assert len(original['files'])==93 and original['source_commit']==SRC
for rel,rec in original['files'].items():assert sha(P/rel)==rec['sha256'],rel
first=B/'reviews/KE05-ie13-continuation-existing'
second=B/'reviews/KE05-mf22-independent'
assert sha(first/'REVIEW.md')=='4f51af5b73157b8683f14ae8b491541e7a16a6bd75fa6aff568b78a98b16b621'
assert sha(first/'CHECKS.json')=='39af5e73a4287f5c0beb8eab84988357552c75046adde809be71c69ba1d01fa0'
assert sha(second/'REVIEW.md')=='ef6d2b6451b7b6099acc7e9603aa8290af74816074517ac256644657d4164752'
assert sha(second/'CHECKS.json')=='b169b47db14de61da246aa263cbe34699994a7c053712068dbe2f7d17c1dbfed'
assert read(first/'CHECKS.json')['all23_same_at_head_and_tested_and_reviewed']
assert read(second/'CHECKS.json')['all_23_Lean_sources_read_and_bound_to_both_Git_commits']
assert read(second/'CHECKS.json')['no_blocking_mathematical_defect_found']
assert sha(second/'MANIFEST.json')=='020ac83824c8f1e7f13b8676cd2aae6899b95fb79e4c6a1235730638baeb22db'
for rel,h in read(second/'MANIFEST.json')['files'].items():assert sha(second/rel)==h,rel
historical=B/'overlap-runs/KE05-34927150695'
audit=read(historical/'ROOT-AUDIT.json')
assert audit['actual_checkout']==TESTED and audit['bound_inputs']==93
assert len(audit['exports'])==10 and audit['default_kernel_and_comparator']=='PASS'
V.mkdir(parents=True)
copy(B/'KE05-IMPORTED-EXACT-SOURCE.json',V/'ORIGINAL-93-INPUTS.json')
for name in ['README.md','formalization.yaml','lakefile.toml']:copy(P/name,V/'before'/name)
first_files=['REVIEW.md','CHECKS.json','ALL-10-HEADERS.json','ALL-23-SOURCE-BINDINGS.json','ACTIVE-IMPORT-CLOSURE.json','LOG-AUTHENTICATION-CHECKS.json','HISTORICAL-ALL-INPUTS.json']
path_map=[]
for label,source,names in [('referee-elimination',first,first_files),('referee-matrix-functions',second,[p.name for p in sorted(second.iterdir()) if p.is_file()])]:
    for name in names:
        target=P/'reviews/campaign'/label/name;copy(source/name,target)
        path_map.append({'source_packet':source.name,'source_file':name,'retained':str(target.relative_to(P)),'sha256':sha(target)})
histdest=V/'historical-run-34927150695'
assert not histdest.exists()
retained_historical={}
for file in sorted(historical.rglob('*')):
    if file.is_file() and file.relative_to(historical).as_posix()!='run.json':
        rel=file.relative_to(historical); copy(file,histdest/rel)
        assert sha(histdest/rel)==sha(file)
        retained_historical[str(rel)]=sha(file)
# The raw run API embeds commit-author contact fields. Keep it private and
# retain a plainly labelled identity/status summary plus its original hash.
raw_run=read(historical/'run.json')
public_keys=['id','name','head_branch','head_sha','run_number','run_attempt','event','status','conclusion','created_at','updated_at','html_url']
dump(histdest/'run-public-summary.json',{'kind':'selected public identity/status fields; not raw API bytes',
    'original_run_API_sha256':sha(historical/'run.json'),
    'omitted':'Raw head_commit/author/committer metadata, including contact email fields.',
    'identity':{key:raw_run[key] for key in public_keys}})
dump(histdest/'RETAINED-EVIDENCE.json',{'byte_exact_retained_files':retained_historical,
    'raw_run_API_omitted_to_avoid_publishing_contact_fields':True,
    'raw_run_API_sha256':sha(historical/'run.json'),
    'public_summary':'run-public-summary.json'})

lake=P/'lakefile.toml'; before=lake.read_text()
assert before.count('defaultTargets = ["Challenge"]')==1
lake.write_text(before.replace('defaultTargets = ["Challenge"]','defaultTargets = ["Solution"]',1))
meta=yaml.safe_load((P/'formalization.yaml').read_text())
assert meta['project']['authors']==['Sidney Holden']
meta['project']['responsible_maintainers']=['George Stepaniants']
meta['project']['affiliations']={'George Stepaniants':'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'}
meta['repository']={'role':'substantive-development','note':'Campaign integration of Sidney Holden’s existing Apache-2.0 formalization. Exact mathematical sources are unchanged; fresh canonical Linux execution on this integration commit is pending.'}
meta['status']['whole_problem_verified']=False
meta['status']['scope']='The complete original target is proved by the unchanged existing formalization and was accepted at historical source '+TESTED+' in run 34927150695. Two new independent complete mathematical and historical-runtime reviews approved all 23 Lean inputs and ten exports. A fresh campaign check of the present integration commit is pending; no canonical status or completed count is promoted here.'
for result in meta['status']['main_results']:
    result['verification_status']='Authenticated historical Linux Comparator/default-kernel acceptance at '+TESTED+'; fresh exact-campaign-commit execution pending.'
meta['review']['notes']+=' Two additional independent nonimplementing campaign referees read the entire 23-file source and independently reconciled the authenticated historical execution. Their reports and source bindings are retained under reviews/campaign. Root prepares integration metadata and the default-target amendment without changing any mathematical file.'
meta['review']['status']='two complete independent campaign source/history approvals; fresh campaign canonical run pending'
meta['automation']['notes']+=' George Stepaniants requested this subsequent upstream integration and verification campaign. Authorship of the reused Lean implementation remains Sidney Holden’s.'
meta['acknowledgements']='Existing Lean formalization by Sidney Holden, Apache-2.0. Mathematical proof by George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology; original framework/conjecture by Nian Shao. Campaign integration and verification submission by George Stepaniants with OpenAI Codex assistance. Mathlib, LeanCert, Lean Comparator and formalization.yaml retain their implementation credits.'
meta['alignment']={'numerical_boundary':'NUMERICAL_TARGETS.md','proposed_statements':'Challenge.lean','implementation_entry':'Solution.lean','source_correspondence':'PROOF_NOTES.md','campaign_import':'verification/campaign-import-2026-09-16/TRANSITION.json'}
jsonschema.Draft7Validator(read(W/'docs/lean/schema/v0.4.schema.json')).validate(meta)
(P/'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+yaml.safe_dump(meta,sort_keys=False,allow_unicode=True,width=100))

(P/'README.md').write_text('''# KE-05 Lean formalization

This project proves the full negative answer to KE-05, retaining the literal matrix recurrence, every root ordering, genuine Euclidean operator norms, independent real standard-Gaussian entries and the original uniform-probability quantifiers. A deterministic family with block size two and three blocks refutes the universal conjecture; no finite-sample or scalar-only claim replaces the matrix theorem.

**Existing formalization: Sidney Holden**, with OpenAI Codex assistance, under [Apache-2.0](LICENSE). **Mathematical proof and this integration/verification submission: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Nian Shao** retains credit for the original framework and conjecture. Integration does not transfer authorship of the existing Lean code. No contact email is published.

The unchanged implementation comes from [Sidney Holden’s immutable source](https://github.com/sidneyholden1/OpenProblemsInNLA/tree/04f3f39beb69d77dbc4a8eadee70259eb89a591a/randomized-and-low-rank-approximation/KE-05/lean). Actual historical [Linux run 34927150695](https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34927150695) accepted all ten exports through LeanCert kernel-trust checks, Comparator, Lean default-kernel replay, standard transitive axioms and the required sandbox/rejection controls at proof revision `9acd5d5c9ab91c5c0c07603b6b48c0cb7ede54e6`. All 23 mathematical files are byte-identical at both revisions. The later historical revision changed only README and formalization metadata inside the project.

**Fresh campaign canonical verification is pending.** Two additional independent nonimplementing AI-agent referees have read the entire proof and original target and separately audited the authenticated historical execution. Their [reviews](reviews/campaign/README.md) and the [import record](verification/campaign-import-2026-09-16/TRANSITION.json) retain exact source/evidence hashes. They inspected a historical execution; this does not claim that a new integration commit has already run. No problem status or campaign count is changed by this candidate.

Read the [numerical targets](NUMERICAL_TARGETS.md), [definitions](NLA/KE05/Definitions.lean), [independent Challenge](Challenge.lean), [proof notes](PROOF_NOTES.md) and all ten [Solution exports](Solution.lean). The historical [statement freeze](verification/statement-freeze.json) remains unchanged. Its earlier Solution-library registration and the current default-target amendment are explicitly recorded; mathematical statements, definitions, dependency pins and Comparator policy are unchanged. Challenge’s ten specification placeholders are never imported by Solution.

Exact two-by-two identities, a proved polynomial null-set theorem for the actual Gaussian law, and measure-theoretic convergence remove interval searches. Ten LeanCert `#assert_trust kernel` checks audit the exported proofs. The permitted axioms are only `propext`, `Classical.choice` and `Quot.sound`; the historical actual run reported these for all ten results.

For a developer build with the pinned dependencies available, run `lake build Solution` from this directory. The documented current default also selects Solution, so plain `lake build` checks the full graph. For authoritative verification use the shared [non-root Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/KE-05/lean /absolute/path/to/nla-lean-tools
```

The harness runs actual Comparator, default-kernel replay and problem-specific controls from committed sources. The current campaign uses remote Linux; no local Lean/Lake execution is claimed. [Metadata](formalization.yaml) follows schema v0.4. Reviews follow the repository’s scoped Tau Ceti adaptation, without claiming official endorsement or external human peer review. The Schiffer and Forsythe examples inform the shared organization and checking protocol.
''')
(P/'reviews/campaign/README.md').write_text('''# Independent KE-05 campaign reviews

Both referees read the complete original target and all 23 mathematical Lean inputs, checked the ten frozen exports, and independently reconciled the authenticated historical Linux execution. Neither authored the proof or ran a fresh Lean process. Their full reports and exact source bindings are retained below. The first packet retains the selected complete report/check/binding records listed in the import map; the second retains its complete sealed top-level packet. Private commit API records were not copied.

- [Elimination referee](referee-elimination/REVIEW.md)
- [Matrix-functions referee](referee-matrix-functions/REVIEW.md)

The existing formalization remains Sidney Holden’s Apache-2.0 work. These are AI-agent reviews under the repository’s scoped protocol, not human peer review. Fresh campaign runtime acceptance remains separate.
''')
dump(V/'RETAINED-REVIEW-PATHS.json',path_map)
protected={rel:rec['sha256'] for rel,rec in original['files'].items() if rel not in ['README.md','formalization.yaml','lakefile.toml']}
assert len(protected)==90
for rel,h in protected.items():assert sha(P/rel)==h,rel
active={rel:rec['sha256'] for rel,rec in original['files'].items() if rel in ['Challenge.lean','Solution.lean'] or (rel.startswith('NLA/') and rel.endswith('.lean'))}
assert len(active)==23
assert [x['declaration'] for x in meta['status']['main_results']]==read(P/'comparator.json')['theorem_names']
email=re.compile(r'[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
email_files=[]
for f in P.rglob('*'):
    if f.is_file() and f.suffix not in ['.zip','.png','.pdf'] and email.search(f.read_text(errors='replace')):
        email_files.append(str(f.relative_to(P)))
assert not email_files,email_files
transition={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_repo':'sidneyholden1/OpenProblemsInNLA','source_commit':SRC,'historical_tested_commit':TESTED,'historical_run':34927150695,'formalization_author':'Sidney Holden','mathematical_author':'George Stepaniants','submission_and_integration_author':'George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology','all23_mathematical_inputs_unchanged':active,'all90_protected_original_inputs_unchanged':protected,'changed_original_inputs':['README.md','formalization.yaml','lakefile.toml'],'default_target_amendment':{'before':sha(V/'before/lakefile.toml'),'after':sha(P/'lakefile.toml'),'exact_change':'defaultTargets = ["Challenge"] -> ["Solution"]; no other build configuration or dependency change'},'all_original93_inputs': 'ORIGINAL-93-INPUTS.json','review_records':'RETAINED-REVIEW-PATHS.json','historical_root_audit_sha256':sha(histdest/'ROOT-AUDIT.json'),'fresh_campaign_Linux_verification':'pending','canonical_status_changed':False,'completed_count_changed':False,'local_Lean_execution':False,'contact_email_added':False}
dump(V/'TRANSITION.json',transition)
copy(Path(__file__),V/'prepare_candidate.py')
manifest={str(f.relative_to(P)):sha(f) for f in sorted(P.rglob('*')) if f.is_file()}
dump(B/'KE05-CAMPAIGN-CANDIDATE.json',{'worktree':str(W),'project':str(P.relative_to(W)),'files':manifest,'protected_original_inputs':90,'mathematical_inputs':23,'exports':10,'fresh_runtime_pending':True})
print(json.dumps({'inputs':len(manifest),'mathematical_sources':23,'candidate_manifest_sha256':sha(B/'KE05-CAMPAIGN-CANDIDATE.json')},indent=2))
