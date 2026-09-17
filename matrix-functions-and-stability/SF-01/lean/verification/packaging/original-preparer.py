"""Gated private SF01 packaging: Python only, no Lean, Git mutation or publishing.

Supply root's actual complete acceptance and its exact assembly/source map.
The script refuses pending or source-mismatched inputs before writing a package.
"""
from pathlib import Path
import argparse,datetime,difflib,hashlib,json,os,re,subprocess,sys
import jsonschema,yaml
B=Path('/tmp/nla-lean-next-20260915').resolve()
W=B/'next-proofs/SF-01'
L=Path('/private/tmp/nla-lean-local-shared-20260916')
I=Path('/private/tmp/nla-lean-next-mf22-worktree')
PERMITTED={'propext','Classical.choice','Quot.sound'}
SCHEMA_SHA='25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
EMAIL=re.compile(rb'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
WRAPPER='NLA/SF01/FinalChecks.lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
canon=lambda p:'Solution.lean' if p==WRAPPER else p

def source_details(rows):
    names=read(W/'comparator.json')['theorem_names'];sources={canon(k):v for k,v in rows.items()}
    texts={k:Path(v['source']).read_text() for k,v in sources.items()};results=[]
    for full in names:
        short=full.removeprefix('NLA.SF01.')
        pat=re.compile(r'(?m)^(?:theorem|lemma)\s+'+re.escape(short)+r'\b')
        hits=[(k,m)for k,t in texts.items()for m in pat.finditer(t)]
        if len(hits)!=1:raise ValueError('Expected one implementation declaration: '+full)
        k,m=hits[0];results.append({'declaration':full,'file':k,'line':texts[k].count('\n',0,m.start())+1,'file_sha256':sources[k]['sha256'],'sorry_count':0,'axioms':[],'comparator_config':'comparator.json','verification_status':'Source preparation only; complete local acceptance and canonical verification pending.'})
    graph={k:[x.replace('.','/')+'.lean'for x in re.findall(r'(?m)^import\s+(\S+)',Path(v['source']).read_text())if x.startswith('NLA.')]for k,v in rows.items()}
    seen=set();todo=[WRAPPER]
    while todo:
        k=todo.pop()
        if k in seen:continue
        if k not in graph:raise ValueError('Missing active import '+k)
        seen.add(k);todo.extend(graph[k])
    return texts,results,sorted(map(canon,seen)),sorted(map(canon,set(rows)-seen))

def metadata_for(results,acceptance=None):
    d=yaml.safe_load((W/'formalization.yaml').read_text())
    d['project']['description']='Full original positive-diagonal real H-matrix Newton theorem, for every positive dimension, every admissible matrix and every iteration. The original complex algebraic spectral-radius predicate and actual inverse availability are retained.'
    d['automation']['methods'][0]['tool_setup']='Parallel source and referee agents; one coordinator-run serial macOS compiler. Fresh non-root Linux default-kernel, Comparator and rejection-control execution is a separate gate.'
    d['automation']['notes']='Substantial OpenAI Codex assistance. Private source and metadata preparation is distinct from actual runtime verification. The package preparer did not implement SF01 mathematics; proof authors and independent reviewers retain their explicit roles. No official Tau Ceti endorsement or human peer review is claimed.'
    d['status']={'scope':'Every real positive-dimensional matrix satisfying the original spectral H predicate and strict positive diagonal, initialized by X0=A, with X(k+1)=(Xk+Xk^-1*A)/2 for every k>=0. Proves H structure, positive diagonal and actual unitness at every iterate.','whole_problem_verified':False,'sorry_count':0,'sorry_in_definitions':0,'axioms':sorted(PERMITTED),'main_results':results,'source_scan_note':'All active implementations are hole-free. Challenge contains24 deliberate specification placeholders and is never imported.'}
    for row in d['related_formalizations']:
        if 'sidneyholden1' in row['id']:row['note']='Two unchanged Apache-2.0 IV03 files by Sidney Holden are genuinely imported. Weighted maximum-principle, unitness and inverse-positivity lemmas are consumed; their original credit and license remain. The new SF01 spectral equivalence is proved separately.'
        if '/alerad/leancert/' in row['id']:row['note']='Kernel-mode exact positivity certificate for one half, consumed by the first iterate and coefficient halving. No variable interval subdivision or input enumeration.'
    d['review']={'status':'Historical full-source and scoped continuation reports retained; final current review/runtime acceptance must be reconciled independently.','reviewers':[],'notes':'See reviews/INDEX.json. Original preparatory statements and dated reports are preserved as historical records, not current verification claims.'}
    d['alignment'].update(active_source_manifest='ACTIVE-SOURCE-MANIFEST.json',implementation_map='IMPLEMENTATION-MAP.json',publication_evidence='PUBLICATION-EVIDENCE.json',reuse_attribution='REUSE-IV03.md')
    d['toolchain']={'lean':(W/'lean-toolchain').read_text().strip(),'dependency_manifest':'lake-manifest.json'}
    d['verification']={'phase':'Pending final local acceptance; template only'if acceptance is None else'Actual complete serial macOS source build accepted; canonical Linux verification pending','canonical_verification_completed':False,'default_kernel':'pending fresh canonical Linux replay','comparator':'pending all24 actual comparisons','sandbox_and_rejection_controls':'pending actual non-root Linux controls','local_acceptance':None if acceptance is None else'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json','numerical_certificate':{'declaration':'NLA.SF01.half_positive_certificate','statement':'(0 : Real) < 1 / 2','method':'interval_decide (trust := kernel)','consumed_by':['initial_data_valid','newton_data_step'],'interval_subdivision':'none; all variable matrix and iteration arguments are symbolic'},'scope_note':'The complete original Newton target is retained; scaled/affine initialization and Halley extensions are not formal claims.','publication':'Private preparation only; no status/count/Git/CI/PR change.'}
    if acceptance is not None:
        for r in results:
            r['axioms']=acceptance['observed_axioms'][r['declaration']]
            r['verification_status']='Actual local compilation and final kernel assertions passed; fresh canonical Linux replay, Comparator and controls pending.'
        d['verification']['local_receipt_sha256']=acceptance['receipt_sha256']
    return d

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-map',required=True,type=Path,help='Exact final coordinator ASSEMBLY JSON')
    ap.add_argument('--acceptance',required=True,type=Path)
    ap.add_argument('--acceptance-sha256',required=True)
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--handoff',required=True,type=Path)
    args=ap.parse_args();P=args.output.resolve();H=args.handoff.resolve();checks=[];bindings={};retained=[];omitted=[]
    def check(q,s):
        if not q:raise ValueError(s)
        checks.append(s)
    def bind(p,h=None):
        p=Path(p).resolve();v=sha(p);check(h is None or v==h,'hash '+str(p));bindings[str(p)]=v;return p
    def put(rel,data):
        p=P/rel;check(not p.exists(),'new path '+rel)
        if isinstance(data,str):data=data.encode()
        check(EMAIL.search(data)is None,'no email '+rel);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    def dump(rel,x):put(rel,json.dumps(x,indent=2,ensure_ascii=False)+'\n')
    def copy(p,rel):
        p=bind(p);put(rel,p.read_bytes());retained.append({'original_path':str(p),'path':rel,'sha256':sha(p)})
    def reference(p,rel,url=None):
        p=bind(p)
        if EMAIL.search(p.read_bytes()):omitted.append({'original_path':str(p),'intended_path':rel,'sha256':sha(p),'immutable_source':url,'reason':'Contact-bearing original reference remains private; no proof source omitted.'})
        else:copy(p,rel)
    check(not P.exists() and not H.exists(),'new output and handoff only')
    check(P.is_relative_to(B) and H.is_relative_to(B),'private campaign paths only')
    a=read(bind(args.acceptance,args.acceptance_sha256));assembly=read(bind(args.source_map,a['assembly_sha256']))
    check(a['reviewer']=='/root' and a['complete_development_graph_passed'],'actual coordinator complete acceptance required')
    check(a['platform']=='darwin' and a['frozen_export_count']==24 and not a['canonical_verification_completed'] and not a['comparator_run'] and a['count_change']==0,'local-only exact24 acceptance')
    rows={k:v for k,v in assembly['sources'].items()if k.startswith(('NLA/SF01/','NLA/IV03/'))}
    check(len(rows)==37 and WRAPPER in rows,'preserve all37 selected source inputs')
    canonical={canon(k):v['sha256']for k,v in rows.items()}
    check({canon(k):h for k,h in a['accepted_source_sha256'].items()}==canonical,'all37 match actual accepted source map')
    for k,v in rows.items():bind(v['source'],v['sha256'])
    texts,results,closure,probes=source_details(rows)
    check(len(closure)==31 and len(probes)==6,'actual final31 import closure plus six historical independent probes')
    cfg=read(bind(W/'comparator.json'));names=cfg['theorem_names']
    check(len(names)==len(set(names))==24 and cfg['definition_names']==[] and set(cfg['permitted_axioms'])==PERMITTED,'exact24 frozen Comparator boundary')
    check(set(a['observed_axioms'])==set(names) and all(set(v)<=PERMITTED for v in a['observed_axioms'].values()),'all24 actual standard axiom sets')
    wrapper=texts['Solution.lean']
    check(re.findall(r'(?m)^import\s+(\S+)',wrapper)==['NLA.SF01.NewtonConclusion'],'export-only wrapper import')
    check('namespace NLA.SF01'in wrapper and re.findall(r'(?m)^#assert_trust kernel (\S+)$',wrapper)==[n.removeprefix('NLA.SF01.')for n in names],'exact namespaced24 trust assertions')
    check(re.findall(r'(?m)^#print axioms (\S+)$',wrapper)==[n.removeprefix('NLA.SF01.')for n in names],'exact24 axiom output requests')
    check(all(not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*axiom\s',t,re.M)for t in texts.values()),'no proof holes native trust or custom axioms')
    check(all('import Challenge'not in t for t in texts.values()),'implementation never imports Challenge')
    freeze=read(bind(W/'STATEMENT-FREEZE.json'));frozen=freeze['frozen_files'];check(len(frozen)==9 and frozen==a['frozen_files_sha256'],'exact frozen9 acceptance')
    for k,h in frozen.items():bind(W/k,h)
    receipt=read(bind(a['receipt'],a['receipt_sha256']));check(bool(receipt.get('end')),'actual complete terminal receipt')
    check(not any(m.startswith(('NLA.SF01.','NLA.IV03.'))for m in receipt['failed_modules']+receipt['blocked_modules']),'no failed or blocked selected components')
    check({p['name']:p['rev']for p in read(W/'lake-manifest.json')['packages']}==a['dependency_commits'],'exact dependency pins')
    command_paths=set();expectedmods={k[:-5].replace('/','.')for k in rows}
    check(set(a['actual_commands'])==expectedmods,'successful origins for all37 retained inputs, including six probes')
    for mod,c in a['actual_commands'].items():
        check(c['exit_code']==0 and c['source_sha256']==rows[mod.replace('.','/')+'.lean']['sha256'],'actual successful origin '+mod)
        rp=bind(c['receipt'],c['receipt_sha256']);lp=bind(c['log'],c['log_sha256']);command_paths.update([rp,lp])
        cr=read(rp);actual=next(x for x in cr['commands']if x['module']==mod)
        check(bool(cr.get('end')) and actual.get('exit_code')==0 and actual['source_sha256']==c['source_sha256'] and actual['log_sha256']==c['log_sha256'],'literal terminal command origin '+mod)
        check('error:'not in lp.read_text(),'successful log '+mod)
    final_log=Path(a['actual_commands']['NLA.SF01.FinalChecks']['log']).read_text()
    axioms={n:[v.strip()for v in raw.split(',')if v.strip()]for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",final_log)}
    check(axioms==a['observed_axioms'],'actual final24 printed axiom sets')
    oldlake=(W/'lakefile.toml').read_bytes();check(oldlake.count(b'defaultTargets = ["Challenge"]')==1 and oldlake.count(b'name = "Solution"')==1,'Solution library already registered')
    newlake=oldlake.replace(b'defaultTargets = ["Challenge"]',b'defaultTargets = ["Solution"]')
    schema=bind(I/'docs/lean/schema/v0.4.schema.json',SCHEMA_SHA);validator=bind(I/'tools/lean/validate_manifest.py')
    metadata=metadata_for(results,a);jsonschema.Draft7Validator(read(schema)).validate(metadata)
    # All acceptance and source guards above complete before any output is written.
    P.mkdir()
    for k,v in rows.items():copy(v['source'],canon(k))
    snap='statement-audit/frozen-35083895041/snapshots/'
    for k,h in frozen.items():
        copy(W/k,snap+k)
        if k not in canonical and k!='lakefile.toml':copy(W/k,k)
    put('lakefile.toml',newlake)
    for fn in ['SOURCE-PROVENANCE.json','STATEMENT-FREEZE.json','REVIEW-PLAN.md','REUSE-IV03.md','STATEMENT-HEADERS.json','DRAFT-CLOSURE.json','STATIC-CHECKS.json']:
        copy(W/fn,fn)
    for fn in ['README.md','formalization.yaml','PROOF-STATUS.md','lakefile.toml']:
        copy(W/fn,'verification/packaging/historical-source/'+fn)
    copy(W/'statement-history/MANIFEST.json','statement-history/MANIFEST.json')
    dump('statement-history/ARCHIVE-SCOPE.json',{'scope':'Exact original preparation inventory retained, not a current package manifest. Frozen amended statements are separately preserved with their actual statement runtime. Historical wording is not current status.','actual_statement_commit':freeze['actual_statement_commit'],'actual_statement_run':freeze['actual_statement_run']})
    sr=B/'development-runs'/str(freeze['actual_statement_run'])
    for src,rel in [(sr/'artifacts/lean-development-statements/receipt.json','receipt.json'),(sr/'ROOT-AUDIT.json','ROOT-AUDIT.json'),(B/'SF01-RA02-STATEMENT-ACCEPTANCE.json','COORDINATOR-ACCEPTANCE.json')]:copy(src,'statement-audit/runtime/'+rel)
    prov=read(W/'SOURCE-PROVENANCE.json')
    for row in prov['canonical']:
        bind(row['private_retained_path'],row['sha256']);reference(row['private_retained_path'],'sources/upstream/'+row['git_path'],'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/'+row['git_commit']+'/'+row['git_path'])
    for row in prov['standards']:
        bind(row['private_retained_path'],row['sha256']);reference(row['private_retained_path'],'sources/standards/'+row['project']+'/'+row['path'],'https://github.com/'+row['project']+'/blob/'+row['commit']+'/'+row['path'])
    for row in prov['structure_examples']:
        bind(row['private_retained_path'],row['sha256']);reference(row['private_retained_path'],'sources/examples/'+Path(row['private_retained_path']).name)
    copy(args.acceptance,'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json')
    command_paths.update([Path(a['receipt']),args.source_map,L/'LOCAL-ENVIRONMENT.json',L/'serial_compile.py',L/'serial_compile_v2.py',L/'serial_compile_v3.py'])
    command_paths.update(Path(p)for p in a['bindings']if Path(p).is_relative_to(L))
    pathmap={}
    for src in sorted(command_paths):
        src=src.resolve();check(src.is_relative_to(L),'local runtime path scope '+str(src));rel='verification/local-development/'+str(src.relative_to(L));copy(src,rel);pathmap[str(src)]={'path':rel,'sha256':sha(src)}
    dump('verification/local-development/PATH-MAP.json',pathmap)
    reviews=[]
    for q in sorted((B/'reviews').iterdir()):
        if not q.is_dir()or not q.name.startswith('SF01-'):continue
        for fn in ['REVIEW.md','NOTE.md','CHECKS.json','MANIFEST.json']:
            if(q/fn).is_file():
                rel='reviews/historical/'+q.name+'/'+fn;reference(q/fn,rel)
                if(P/rel).exists()and fn in ['REVIEW.md','NOTE.md']:reviews.append({'path':rel,'sha256':sha(q/fn),'scope':'Exact original report role and time; not automatically current final approval.'})
    dump('reviews/INDEX.json',{'reports':reviews,'scope':'Bounded exact historical reports/checks; original private inventories retain their original scope. Final complete-source and runtime acceptance remains a coordinator gate.','preparer_role':'SF01 metadata preparer and nonauthor mathematical source referee; not an independent referee of its own packaging.','canonical_runtime':'pending','official_Tau_Ceti_or_human_endorsement':False})
    dump('ACTIVE-SOURCE-MANIFEST.json',{'problem_id':'SF-01','source_sha256':canonical,'retained_Lean_files':37,'final_transitive_import_closure':closure,'older_independent_export_probes':probes,'wrapper_transport':'FinalChecks -> Solution, exact bytes','local_acceptance_sha256':args.acceptance_sha256,'canonical_verification_completed':False,'whole_problem_verified':False})
    dump('IMPLEMENTATION-MAP.json',{'exports':results,'source_sha256':canonical,'status':'Local source compilation accepted; actual canonical Comparator identity pending'})
    put('verification/packaging/LAKE-DEFAULT.patch',''.join(difflib.unified_diff(oldlake.decode().splitlines(True),newlake.decode().splitlines(True),fromfile='frozen/lakefile.toml',tofile='lakefile.toml')))
    dump('verification/packaging/TRANSITION.json',{'all37_Lean_bytes_unchanged':True,'only_filename_transport':'NLA/SF01/FinalChecks.lean -> Solution.lean','frozen9_originals':frozen,'active_Lake_only_change':'defaultTargets Challenge -> Solution; existing Solution library retained','active_lake_sha256':hashlib.sha256(newlake).hexdigest(),'proof_pin_harness_resource_change':False,'Git_CI_publication_count_action':False})
    dump('verification/OMITTED-ORIGINALS.json',{'privacy_omissions':omitted,'scope':'No active proof or frozen contract omitted. Contact-bearing external originals are hash-bound and linked. Raw GitHub API payloads, full fork trees and recursive private archives remain private.'})
    dump('PUBLICATION-EVIDENCE.json',{'phase':'Actual local development accepted; private canonical candidate','local_acceptance':'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json','local_acceptance_sha256':args.acceptance_sha256,'source_map':'ACTIVE-SOURCE-MANIFEST.json','review_index':'reviews/INDEX.json','canonical_verification_completed':False,'remaining_gates':['current two nonauthor complete-source reviews','independent package review','fresh non-root Linux default-kernel/Comparator/axiom/LeanCert/control verification','actual runtime source authentication and referees','publication documents and exact publication commit rerun','individual upstream main PR and its actual CI'],'status_count_or_publication_change':False})
    put('formalization.yaml','# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+yaml.safe_dump(metadata,sort_keys=False,allow_unicode=True,width=100))
    put('README.md',README)
    copy(schema,'verification/packaging/v0.4.schema.json');dump('verification/RETAINED-PATHS.json',retained)
    result=subprocess.run([sys.executable,str(validator),str(P)],capture_output=True,text=True)
    put('verification/packaging/schema-validation.log',result.stdout+result.stderr);check(result.returncode==0,'actual shared schema and24-target coverage validation')
    for k,h in canonical.items():check(sha(P/k)==h,'final source '+k)
    for k,h in frozen.items():check(sha(P/(snap+k))==h,'final frozen snapshot '+k)
    for p in P.rglob('*'):
        if p.is_file():check(EMAIL.search(p.read_bytes())is None,'final no-email '+str(p.relative_to(P)))
    dump('PACKAGE-MANIFEST.json',{'phase':'actual local development accepted; canonical verification pending','files':{str(p.relative_to(P)):sha(p)for p in sorted(P.rglob('*'))if p.is_file()}})
    H.mkdir();(H/'CHECKS.json').write_text(json.dumps({'preparer':'/root/mf22_publication_referee','checks':checks,'package_manifest_sha256':sha(P/'PACKAGE-MANIFEST.json'),'schema_exit_code':result.returncode,'new_Lean_execution':False,'Git_or_count_action':False},indent=2)+'\n')
    (H/'BINDINGS.json').write_text(json.dumps({os.path.relpath(p,H):h for p,h in bindings.items()},indent=2)+'\n')
    (H/'MANIFEST.json').write_text(json.dumps({'files':{p.name:sha(p)for p in sorted(H.iterdir())if p.is_file()},'preparer':{'path':str(Path(__file__).resolve()),'sha256':sha(__file__)},'package_manifest_sha256':sha(P/'PACKAGE-MANIFEST.json')},indent=2)+'\n')
    print(json.dumps({'package_manifest':sha(P/'PACKAGE-MANIFEST.json'),'handoff_manifest':sha(H/'MANIFEST.json'),'checks':len(checks)},indent=2))

README='''# SF-01 Lean formalization

This candidate proves preservation of positive-diagonal real H-matrices by the original Newton iteration: X0=A and X(k+1)=(Xk+Xk^-1*A)/2. It includes every positive dimension and every k>=0, and proves actual invertibility at every step. The H predicate uses the original comparison matrix and full complex algebraic spectral radius. No symmetry, normality, positive entries, bounded iteration or supplied rational representation is assumed.

**Actual local Lean build accepted; canonical Linux verification pending.** The [local acceptance](verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json) and [command-origin map](verification/local-development/PATH-MAP.json) identify exact successful sources and logs, including reused successful local outputs. They do not certify the fresh non-root Linux sandbox, default-kernel replay, Comparator or rejection controls. Those remain separate gates. No verified count, published commit or PR is claimed by this candidate.

Read the [numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/SF01/Definitions.lean), independent [Challenge](Challenge.lean), and [source correspondence](SourceCorrespondence.md). Frozen preparation records retain historical wording; [publication evidence](PUBLICATION-EVIDENCE.json) records the current phase. All24 exported signatures are selected by [comparator.json](comparator.json), with no replaceable definitions and only propext, Classical.choice and Quot.sound permitted. Deliberate Challenge placeholders are specifications and are never imported by the implementation.

The argument proves the spectral/positive-weight bridges, actual shifted resolvent domination, the finite rational preserver, and a finite positive-definite pole construction. Genuine block inverse identities give a new scalar data record before quantifying over input matrices and dimensions. This yields the all-iteration theorem. Empty pole families, repeated poles and zero weights remain included. Scaled/affine initializations and Halley extensions of the manuscript are outside this formal claim.

The sole interval certificate, `0 < 1/2`, is proved with LeanCert kernel trust and consumed in initialization and coefficient halving. All matrix, dimension, spectral and iteration estimates are symbolic; no interval subdivision or input sampling occurs.

[Solution](Solution.lean) retains exactly the final tested export-only wrapper bytes. Its actual import closure has31 files; all37 selected sources are retained, including six older independent export probes. The [active manifest](ACTIVE-SOURCE-MANIFEST.json) distinguishes them. All nine original frozen files are preserved; the only active Lake change selects the already registered Solution library. With pinned dependencies available, run `lake build` from this directory. Standalone canonical packaging still needs actual Linux execution.

From the repository root, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-functions-and-stability/SF-01/lean /absolute/path/to/nla-lean-tools
```

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematics: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Sidney Holden** retains authorship and Apache-2.0 credit for the two unchanged [IV03 source files](REUSE-IV03.md), which are actually imported. Substantial OpenAI Codex assistance is disclosed. [Historical reports](reviews/INDEX.json) preserve reviewer roles and scopes; no official Tau Ceti endorsement or human peer review is asserted. Schiffer, Forsythe, Mathlib, LeanCert, Lean Comparator and formalization.yaml supplied structure and foundations. [Privacy omissions](verification/OMITTED-ORIGINALS.json) retain exact source hashes and immutable links. [License](LICENSE).
'''
if __name__=='__main__':main()
