#!/usr/bin/env python3
"""Read-only canonical package audit; no Lean, Lake, Git, network or preparer invocation."""
from pathlib import Path
import datetime, difflib, hashlib, json, re, runpy
import yaml

B=Path('/tmp/nla-lean-next-20260915')
S=B/'next-proofs/MI-13'
P=B/'MI13-canonical-package-local53'
F=B/'reviews/MI13-full-referee1-20260917'
F2=B/'reviews/MI13-full-referee2-20260917'
H=P/'verification/packaging/before-final-review-acceptance'
L=Path('/private/tmp/nla-lean-local-shared-20260916')
R=Path(__file__).resolve().parent
checks,bindings=[],{}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(n,c):
    if not c:raise AssertionError(n)
    checks.append(n)
def bind(p,h=None):
    p=Path(p).resolve();value=sha(p)
    check('bound bytes: '+str(p),h is None or value==h)
    check('stable repeated binding: '+str(p),str(p) not in bindings or bindings[str(p)]==value)
    bindings[str(p)]=value
    return value
def read(p):bind(p);return json.loads(Path(p).read_text())
def write(n,data):
    q=R/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def copy(p,n):
    bind(p);q=R/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(Path(p).read_bytes())
def payload_manifest(root,name='MANIFEST.json',expected=None):
    mp=root/name;bind(mp,expected);obj=read(mp);files=obj.get('files',obj.get('payloads'))
    check('exact manifest inventory '+str(root),set(files)=={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p!=mp})
    for rel,h in files.items():bind(root/rel,h['sha256'] if isinstance(h,dict) else h)
    return files

final_files=payload_manifest(P,'PACKAGE-MANIFEST.json','95ac5a2fe203bb712cc29679e867aefdcc5679fceb0d9cceefba39e07e890579')
first_pass_manifest=read(R/'history/pass1/PACKAGE-MANIFEST.json')['files']
check('only one README changes after first successful audit',
      {rel for rel,h in first_pass_manifest.items() if final_files[rel]!=h}=={'README.md'})
check('only the before-README snapshot is added after first audit',
      set(final_files)-set(first_pass_manifest)=={'verification/packaging/before-square-contraction-clarification.md'})
before_square=P/'verification/packaging/before-square-contraction-clarification.md'
bind(before_square,first_pass_manifest['README.md'])
check('exact square-contraction precision change',
      (P/'README.md').read_text()==before_square.read_text().replace(
      'Every contraction is the average of two unitaries.',
      'Every square contraction is the average of two unitaries.'))
bind(H/'PACKAGE-MANIFEST.json','2251537cdad61b7a3dc41c99281832550102bb490af711fb9ecff2ec7d0ac238')
original_files=read(H/'PACKAGE-MANIFEST.json')['files']
for rel,h in original_files.items():
    bind(H/rel if rel in {'README.md','formalization.yaml','STATE.json'} else P/rel,h)
check('initial 439-payload package fully reconstructed',len(original_files)==439)
proof_files=payload_manifest(F,expected='d18067284ba82179c5e55803d466afbe020abfd7eb81b219d664564023cddc0e')
proof2_files=payload_manifest(F2,expected='f6779a9f442fec977efb548685bfbb83b43aec88ba3fe9495e0125b7117cd9d3')
old_bindings=read(F/'BINDINGS.json')
for p,h in old_bindings.items():bind(p,h)
other_bindings=read(F2/'FINAL-BINDINGS.json')['bindings']
for p,h in other_bindings.items():bind(p,h)
source_map=read(F/'SOURCE-MAP.json')['files']
active=read(P/'ACTIVE-SOURCE-MANIFEST.json')
check('22 exact independently approved source files',len(source_map)==22 and active['source_sha256']==source_map)
active_lean={str(p.relative_to(P)) for p in P.rglob('*.lean')}
check('exactly 23 active Lean files',active_lean==set(source_map)|{'Challenge.lean'})
for rel,h in source_map.items():bind(P/rel,h);bind(S/rel,h)
check('active manifest local-only status',active['Solution_closure_files']==22 and active['local_run']==53
      and active['canonical_Linux_verification']=='pending')
freeze=read(P/'STATEMENT-FREEZE.json')
bind(P/'STATEMENT-FREEZE.json','bddc9d048f92e28dd8912f9bfb8293e12f07f2458fe7fb5a77e5b3c57e16e732')
check('13 exact frozen inputs recorded',len(freeze['frozen_files'])==13)
for rel,h in freeze['frozen_files'].items():
    original=P/'statement-history/frozen-handoff/lakefile.toml' if rel=='lakefile.toml' else P/rel
    bind(original,h);bind(S/rel,h)
bind(P/'Challenge.lean',active['frozen_Challenge_sha256'])
oldlake=(S/'lakefile.toml').read_text();newlake=(P/'lakefile.toml').read_text()
check('only permitted operational Lake registration',newlake==oldlake.replace('defaultTargets = ["Challenge"]',
      'defaultTargets = ["Solution"]')+'\n[[lean_lib]]\nname = "Solution"\n')
lake_diff=''.join(difflib.unified_diff(oldlake.splitlines(True),newlake.splitlines(True),
      fromfile='frozen/lakefile.toml',tofile='lakefile.toml'))
check('literal retained Lake diff',lake_diff==(P/'verification/packaging/LAKE-REGISTRATION.patch').read_text())
transition=read(P/'verification/packaging/TRANSITION.json')
check('transition hashes and scope exact',transition['frozen13']==freeze['frozen_files']
      and transition['active_lake_sha256']==sha(P/'lakefile.toml')
      and transition['mathematical_sources_unchanged'] is True and transition['Linux_Comparator_run'] is False)

retained=read(P/'verification/RETAINED-PATHS.json')
check('unique retained destination paths',len({x['path'] for x in retained})==len(retained))
original_workspace_paths=set();copied_paths=set();renamed=[]
for row in retained:
    old=Path(row['original_path']);new=P/row['path']
    check('copied destination within package',new.resolve().is_relative_to(P.resolve()))
    bind(old,row['sha256']);bind(new,row['sha256']);copied_paths.add(row['path'])
    if old.resolve().is_relative_to(S.resolve()):
        rel=str(old.resolve().relative_to(S.resolve()));original_workspace_paths.add(rel)
        if rel in {'README.md','formalization.yaml','STATE.json','WORKSPACE-MANIFEST.json','lakefile.toml'}:
            target='statement-history/frozen-handoff/'+rel
        elif old.suffix=='.lean' and rel not in source_map and rel!='Challenge.lean':
            target=rel+'.txt';renamed.append({'before':rel,'after':target,'sha256':row['sha256']})
        else:target=rel
        check('exact archival path transformation '+rel,row['path']==target)
check('every original workspace file retained',original_workspace_paths=={str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()})
generated=set(original_files)-copied_paths
check('11 explicit generated payloads',generated=={'lakefile.toml','formalization.yaml','README.md','STATE.json',
 'ACTIVE-SOURCE-MANIFEST.json','IMPLEMENTATION-MAP.json','verification/packaging/LAKE-REGISTRATION.patch',
 'verification/packaging/TRANSITION.json','verification/RETAINED-PATHS.json',
 'verification/local-development/PATH-MAP.json','verification/local-development/COMMAND-ORIGINS.json'})
check('no compiled outputs or links in source package',not list(P.rglob('*.olean')) and not any(p.is_symlink() for p in P.rglob('*')))
write('ARCHIVE-CORRESPONDENCE.json',{'copied_payloads':len(retained),'original_workspace_files':len(original_workspace_paths),
    'inactive_Lean_renames':renamed,'generated_payloads':sorted(generated),
    'historical_manifest_scope':'Original nested manifests retain original paths. Their original locations and byte-preserving package paths are related by RETAINED-PATHS, not silently rewritten.'})

meta_path=P/'formalization.yaml';bind(meta_path)
validator=P/'sources/standards/completed-project-validator.py.txt'
schema=P/'sources/standards/v0.4.schema.json'
bind(validator,'31e473132c1e8a40c29f73eff01fbff0bafe85649da601d2f550cef164debeb1')
bind(schema,'25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce')
namespace=runpy.run_path(str(validator),run_name='retained_manifest_checker')
namespace['validate'](P,read(schema))
check('actual unchanged v0.4 schema and 36-result validator returned normally',True)
meta=yaml.load(meta_path.read_text(),Loader=namespace['UniqueSafeLoader'])
results=meta['status']['main_results'];mapping=read(P/'IMPLEMENTATION-MAP.json')['results'];cfg=read(P/'comparator.json')
check('metadata and implementation-map entries identical',results==mapping)
names=cfg['theorem_names'];check('36 ordered unique exact results',[r['declaration'] for r in results]==names and len(set(names))==36)
frozen_headers=read(F/'EXACT-HEADERS.json')
header_by_name={x['name']:x for x in frozen_headers}
root_report=read(P/'verification/LOCAL-COMPLETE.json')
bind(P/'verification/LOCAL-COMPLETE.json','22930d6b38d589b7fe194746bc5f5ea4ecfc531c0dc0bb4c5916bf06fcdfd4cc')
for result in results:
    rel=result['file'];name=result['declaration'];short=name.split('.')[-1];text=(P/rel).read_text()
    check('correct result file digest '+name,result['file_sha256']==source_map[rel])
    declaration=re.search(r'^theorem '+re.escape(short)+r'\b.*?(?=\s*:=\s*by\b)',text,re.M|re.S)
    check('actual defining line '+name,declaration is not None and text[:declaration.start()].count('\n')+1==result['line'])
    check('frozen exact result header '+name,declaration.group(0).rstrip()==header_by_name[name]['header'])
    check('measured per-result axioms '+name,result['axioms']==root_report['observed_axioms'][name]
          ==['propext','Classical.choice','Quot.sound'])
    check('honest local-only result status '+name,result['verification_status']==
          'Actual source-bound local Lean elaboration and kernel trust assertions passed. Fresh Linux Comparator and isolation checks pending.')
check('all current final-runtime gates pending',all(meta['verification'][k]=='pending' for k in
      ['Linux_Comparator','default_kernel_replay','sandbox_and_rejection_controls']))
check('whole target not counted complete',meta['status']['whole_problem_verified'] is False)
state=read(P/'STATE.json')
check('state only local success',state['local_run']==53 and state['contracts']==36 and state['LeanCert_executed_locally']
      and state['Comparator_executed'] is False and state['published'] is False and state['count_change']==0)
historical_meta=yaml.load((H/'formalization.yaml').read_text(),Loader=namespace['UniqueSafeLoader'])
check('initial review acceptance honestly pending',historical_meta['review']['reviewers']==[]
      and 'pending coordinator acceptance' in historical_meta['review']['status'])
check('current review acceptance only two source reports',meta['review']['reviewers']==
      ['/root/sf_ra_runtime_referee','/root/mi13_full_referee2']
      and 'package' in meta['review']['status'] and 'in progress' in meta['review']['status'])
check('all 36 result metadata unchanged during review acceptance',results==historical_meta['status']['main_results'])
check('precise required contribution credit','George Stepaniants' in meta['project']['authors']
      and 'Department of Computing and Mathematical Sciences, California Institute of Technology'
          in meta['project']['affiliations']['George Stepaniants'])
check('retained source relationships and authorship',len(meta['sources'])==4 and
      any(x.get('authors')==['M. Nobori'] for x in meta['sources']) and
      any(x.get('authors')==['K. M. R. Audenaert'] and x['relationship']=='independently-proves' for x in meta['sources']))
write('METADATA-RESULTS.json',{'schema_sha256':sha(schema),'validator_sha256':sha(validator),'validator_scope':
      'Exact unchanged validate(project,schema) function invoked via runpy with a non-main name; no compilation or network.',
      'all36_results':results,'operational_metadata':{k:v for k,v in meta.items() if k!='status'},
      'no_proof_acceptance_inferred_from_schema':True})

pathmap=read(P/'verification/local-development/PATH-MAP.json')
for source,row in pathmap.items():bind(source,row['sha256']);bind(P/row['path'],row['sha256'])
traces=read(F/'REUSE-CHAINS.json')
for node in traces:
    original=str(L/f"runs/development-{node['run']:02d}/RECEIPT.json")
    check('every approved reuse-node receipt retained '+str((node['run'],node['module'])),original in pathmap)
origins=read(P/'verification/local-development/COMMAND-ORIGINS.json')
approved_runtime=read(F/'RUNTIME.json');expected_origins=approved_runtime['current_origins']
check('exact 22 command origins',set(origins)==set(expected_origins))
for module,c in origins.items():
    original=Path(c['receipt']);k=int(original.parent.name.removeprefix('development-'))
    check('correct fresh origin '+module,k==expected_origins[module])
    receipt=read(original)
    actual=next(x for x in receipt['commands'] if x['module']==module)
    check('literal source command and measured fields '+module,all(c[key]==value for key,value in actual.items()))
    check('actual successful output source '+module,c['exit_code']==0
          and c['source_sha256']==source_map[module.replace('.','/')+'.lean'])
    bind(c['receipt'],c['receipt_sha256']);bind(c['log'],c['log_sha256'])
    for key in ['receipt','log']:
        check('origin '+key+' retained '+module,c[key] in pathmap and pathmap[c[key]]['sha256']==c[key+'_sha256'])
    copied_log=(P/pathmap[c['log']]['path']).read_text()
    check('origin log clean '+module,not re.search(r'warning:|error:|sorryAx|ofReduceBool',copied_log))
final_source=str(L/'runs/development-53/RECEIPT.json')
final=read(P/pathmap[final_source]['path'])
check('actual mixed53 scope disclosed in root report',root_report['mixed_run_total_modules']==24
      and root_report['MI13_selected_modules']==22 and final['completed_modules']==24
      and final['failed_modules']==[] and final['blocked_modules']==[])
check('actual final53receipt is approved one',sha(P/pathmap[final_source]['path'])==
      'a5027742b5bbd84bcc40f077696d3ba203b6f4220c33608cd89dd4ed52448711')
write('RUNTIME-CORRESPONDENCE.json',{'origin_count':len(origins),'copied_local_paths':len(pathmap),
    'approved_reuse_nodes_with_retained_receipts':len(traces),'actual_serial_run':53,
    'total_serial_modules':24,'MI13_scope':22,'excluded_modules':['NLA.IE02.Definitions','NLA.IE02.Coefficients'],
    'scope':'Copied bytes and origin/reuse correspondence only; prior full proof packet provides the independent full execution-evidence audit. No fresh execution.'})

# Authenticate the published subset of both original full packets. The private
# originals remain the authoritative inventories, not the renamed public trees.
review_copies=read(P/'reviews/RETAINED-PATHS.json')
omissions=read(P/'reviews/OMITTED-OUTPUTS.json')
original_review_files={str(q.resolve()) for root in [F,F2] for q in root.rglob('*') if q.is_file()}
listed_review_files=set();review_destinations=set();review_renames=[]
for row in review_copies:
    old=Path(row['original_path']).resolve();new=P/row['path']
    parent=F.resolve() if old.is_relative_to(F.resolve()) else F2.resolve()
    check('review origin belongs to one of two packets',old.is_relative_to(parent))
    rel=str(old.relative_to(parent));expected='reviews/final/'+parent.name+'/'+rel
    if old.suffix=='.lean':expected+='.txt';review_renames.append(row['path'])
    check('exact review archival path transformation '+rel,row['path']==expected)
    check('review copied once '+str(old),str(old) not in listed_review_files and row['path'] not in review_destinations)
    bind(old,row['sha256']);bind(new,row['sha256'])
    listed_review_files.add(str(old));review_destinations.add(row['path'])
for row in omissions:
    old=Path(row['original_path']).resolve();new=P/row['intended_path']
    check('only original referee1 compiled outputs omitted',old.is_relative_to((F/'evidence/outputs').resolve()) and old.suffix=='.olean')
    check('exact omitted output destination',row['intended_path']=='reviews/final/'+F.name+'/'+str(old.relative_to(F.resolve())))
    check('omitted output absent from canonical package',not new.exists())
    check('omitted path not also copied',str(old) not in listed_review_files)
    bind(old,row['sha256']);listed_review_files.add(str(old))
check('every file of both complete review packets accounted for',listed_review_files==original_review_files)
check('exact 653 review copies and 22 binary omissions',len(review_copies)==653 and len(omissions)==22)
check('all 118 historical Lean review snapshots inactive',len(review_renames)==118)
check('exact review/final inventory',review_destinations=={str(q.relative_to(P)) for q in (P/'reviews/final').rglob('*') if q.is_file()})
review_index=read(P/'reviews/INDEX.json')
check('index explicitly scopes original manifests and excludes official endorsement',
      review_index['official_Tau_Ceti_or_human_peer_review'] is False
      and 'private-packet' in review_index['original_manifests'])
for number,(ref,manifest,bindings_count) in enumerate([(F,proof_files,len(old_bindings)),(F2,proof2_files,len(other_bindings))],1):
    report=review_index['reports'][number-1];root_record=P/f'verification/MI13-ROOT-REFEREE{number}-ACCEPTANCE.json'
    bind(P/report['report'],report['report_sha256']);bind(ref/'MANIFEST.json',report['original_manifest_sha256'])
    acceptance=read(root_record);bind(B/root_record.name,sha(root_record))
    check('root acceptance binds report and measured packet counts '+str(number),acceptance['full_REPORT_read'] is True
        and acceptance['report_sha256']==report['report_sha256']
        and acceptance['manifest_sha256']==report['original_manifest_sha256']
        and acceptance['payloads_rehashed']==len(manifest) and acceptance['bindings_rehashed']==bindings_count
        and acceptance['count_change']==0)
final_transition=read(P/'verification/packaging/FINAL-REVIEW-TRANSITION.json')
check('only metadata/copies recorded after initial package',final_transition['active_Lean_bytes_changed'] is False
      and final_transition['frozen_mathematical_inputs_changed'] is False
      and final_transition['review_source_copy_count']==len(review_copies)
      and final_transition['binary_output_omissions']==len(omissions)
      and final_transition['Linux_checks']=='pending' and final_transition['count_change']==0)
check('harness command directory correction made','From the repository root, final Linux verification uses'
      in (P/'README.md').read_text())
check('preparer count clarification is explicit','directory entries, not files' in
      final_transition['initial_preparer_stdout_files_label'])
check('new status prose is readable',all(t not in (P/'formalization.yaml').read_text() for t in
      ['all22implementationinputs','all36exactcontracts']) and all('of22final53Leaninputs' not in row['scope']
      for row in review_index['reports']) and 'contains439' not in final_transition['initial_preparer_stdout_files_label'])
for rel in ['README.md','formalization.yaml','STATE.json']:
    q=R/'diffs'/Path(rel+'.patch');q.parent.mkdir(parents=True,exist_ok=True)
    q.write_text(''.join(difflib.unified_diff((H/rel).read_text().splitlines(True),(P/rel).read_text().splitlines(True),
      fromfile='initial/'+rel,tofile='current/'+rel)))
public_audit=P/'verification/MI13-IE02-PUBLIC-AUDIT-ROOT.json'
bind(B/public_audit.name,sha(public_audit))
public_summary=read(public_audit)
check('limited public-search summary retains explicit exclusions',public_summary['count_change']==0
      and 'private/deleted' in public_summary['scope_limits'] and 'generically named' in public_summary['scope_limits'])
write('PUBLIC-REVIEW-CORRESPONDENCE.json',{'retained_review_copies':len(review_copies),
    'compiled_output_omissions':len(omissions),'inactive_Lean_review_snapshots':len(review_renames),
    'first_packet_payloads_and_bindings':[len(proof_files),len(old_bindings)],
    'second_packet_payloads_and_bindings':[len(proof2_files),len(other_bindings)],
    'root_report_acceptance_records_authenticated':2,
    'public_search_scope':'Authenticated root summary copy and read explicit limits; no fresh network search or independent search completeness claim.'})

scanned=0;contacts=[]
for p in P.rglob('*'):
    if not p.is_file():continue
    scanned+=1
    if re.search(rb'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}',p.read_bytes()):contacts.append(str(p.relative_to(P)))
check('no contact-address pattern in all package files',not contacts)
write('CONTACT-SCAN.json',{'files_scanned':scanned,'files_with_contact_patterns':contacts})
for f in [B/'MI13-package-plan/PLAN.md',B/'MI13-package-plan/prepare.py']:
    copy(f,'evidence/preparer/'+f.name)
for rel in ['PACKAGE-MANIFEST.json','ACTIVE-SOURCE-MANIFEST.json','IMPLEMENTATION-MAP.json','README.md','formalization.yaml',
 'STATE.json','lakefile.toml','STATEMENT-FREEZE.json','comparator.json','verification/packaging/TRANSITION.json',
 'verification/packaging/LAKE-REGISTRATION.patch','verification/RETAINED-PATHS.json','verification/local-development/PATH-MAP.json',
 'verification/local-development/COMMAND-ORIGINS.json','verification/LOCAL-COMPLETE.json']:
    copy(P/rel,'evidence/final-package/'+rel)
for rel in ['PACKAGE-MANIFEST.json','README.md','formalization.yaml','STATE.json']:
    copy(H/rel,'evidence/initial-package/'+rel)
for q in (P/'verification/packaging').rglob('*'):
    if q.is_file():copy(q,'evidence/final-package/'+str(q.relative_to(P)))
for rel in ['reviews/README.md','reviews/INDEX.json','reviews/RETAINED-PATHS.json','reviews/OMITTED-OUTPUTS.json',
      'verification/MI13-ROOT-REFEREE1-ACCEPTANCE.json','verification/MI13-ROOT-REFEREE2-ACCEPTANCE.json',
      'verification/MI13-IE02-PUBLIC-AUDIT-ROOT.json']:
    copy(P/rel,'evidence/final-package/'+rel)
for rel in ['MANIFEST.json','REVIEW.md','AUDIT.json','SOURCE-MAP.json']:
    copy(F/rel,'evidence/prior-proof-review/'+rel)
for p,h in list(bindings.items()):check('final bound bytes stable '+p,sha(p)==h)
write('BINDINGS.json',bindings);write('CHECKS.json',checks)
result={'reviewer':'/root/sf_ra_runtime_referee','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict':'APPROVE canonical source/metadata/evidence packaging at the exact bound candidate; Linux and publication acceptance remain pending.',
    'checks':len(checks),'bindings':len(bindings),'initial_package_payloads':len(original_files),
    'final_package_payloads':len(final_files),'final_package_manifest_sha256':sha(P/'PACKAGE-MANIFEST.json'),'active_Lean_files':len(active_lean),
    'implementation_inputs':22,'frozen_contracts':36,'unchanged_active_frozen_files':12,'documented_operational_Lake_change':1,
    'retained_copies':len(retained),'inactive_Lean_renames':len(renamed),'own_full_proof_packet_payloads_reauthenticated':len(proof_files),
    'own_full_proof_bindings_reauthenticated':len(old_bindings),'schema_and_36result_validator_actually_executed':True,
    'compiler_or_Git_or_network_invoked':False,'final_review_copy_and_acceptance_metadata_followup':'authenticated and accepted',
    'Linux_Comparator_or_publication_acceptance':False,'count_change':0}
write('AUDIT.json',result);print(json.dumps(result,indent=2))
