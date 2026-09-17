from pathlib import Path
import json, hashlib, re, subprocess, sys, os, datetime
import yaml
B=Path('/tmp/nla-lean-next-20260915'); P=B/'MI04-canonical-package-local06'; H=B/'MI04-canonical-local06-handoff'; O=B/'reviews/MI04-mf22-canonical-package-local06'; I=Path('/private/tmp/nla-lean-next-mf22-worktree')
bindings={}; checks=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def bind(p,h=None):
 p=Path(p); actual=sha(p); assert h is None or h==actual,('hash mismatch',str(p),h,actual);bindings[str(p.resolve())]=actual;return p
def read(p):return json.loads(bind(p).read_text())
def ok(b,s):assert b,s;checks.append(s)
manifest=read(P/'PACKAGE-MANIFEST.json');ok(sha(P/'PACKAGE-MANIFEST.json')=='d6dd73000f00186f93c42145ec7def3f7140b881caa2607ba4b537c332f6fc39','exact requested package manifest')
actual={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}
ok(actual==set(manifest['files'])|{'PACKAGE-MANIFEST.json'},'exact 221-file package closure')
for p,h in manifest['files'].items():bind(P/p,h)
hm=read(H/'MANIFEST.json');ok(sha(H/'MANIFEST.json')=='452738ff41ab53e95e0ba5801daae08b2235fed1f29006adbdc7a56e3e84313a','requested handoff manifest')
for p,h in hm['files'].items():bind(H/p,h)
for key in ['preparer_script','package_manifest']:bind(hm[key]['path'],hm[key]['sha256'])
for p,h in read(H/'BINDINGS.json').items():bind(H/p,h)
for row in read(P/'verification/RETAINED-PATHS.json'):
 bind(row['original_path'],row['sha256']);bind(P/row['retained_path'],row['sha256'])
ok(True,'all 206 retained records have exact original and package bytes')
A=read(P/'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json');bind(B/'MI04-LOCAL-DEVELOPMENT-ACCEPTANCE.json',sha(P/'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json'))
S=A['accepted_source_sha256'];ok(len(S)==21,'21 exact active mathematical inputs')
for rel,h in S.items():bind(P/rel,h);bind(A['selected_source_locations'][rel],h)
for rel in ['ACTIVE-SOURCE-MANIFEST.json','IMPLEMENTATION-MAP.json']:ok(read(P/rel)['source_sha256']==S,'same accepted source map '+rel)
C=read(B/'inequalities/MI-04/proof-handoffs/local-diagonalization-03/FINAL-CLOSURE.json')
ok(C['all_active_sources']==S,'current reviewed local-diagonalization closure matches all 21 package inputs')
F=read(P/'STATEMENT-FREEZE.json');ok(F['frozen_files_sha256']==A['frozen_files_sha256'],'ten frozen boundary hashes match actual local acceptance')
for rel,h in F['frozen_files_sha256'].items():
 snap=bind(P/'statement-audit/snapshots'/rel,h)
 if rel!='lakefile.toml':bind(P/rel,h)
 else:ok((P/rel).read_bytes()==snap.read_bytes().replace(b'defaultTargets = ["Challenge"]',b'defaultTargets = ["Solution"]'),'only declared default Lake target changes')
pm=read(P/'verification/local-development/PATH-MAP.json')
for old,row in pm.items():bind(old,row['sha256']);bind(P/row['path'],row['sha256'])
for old,h in A['bindings'].items():bind(old,h);bind(P/pm[old]['path'],h)
origin=[]
for module,c in A['actual_commands'].items():
 recpath=bind(P/pm[c['receipt']]['path'],c['receipt_sha256']);rec=read(recpath)
 log=bind(P/pm[c['log']]['path'],c['log_sha256']);txt=log.read_text()
 ok(not re.search(r'\berror:|sorryAx|Lean\.ofReduceBool',txt),'no actual error or nonstandard trust in accepted log '+module)
 if module=='NLA.MI04.Quadratic':entry=rec
 else:
  entries=[r for r in rec['commands'] if r['module']==module and r.get('exit_code')==0];ok(len(entries)==1,'one actual successful command '+module);entry=entries[0]
 for key in ['exit_code','source_sha256','output_sha256','argv']:ok(entry[key]==c[key],'actual command '+module+' '+key)
 if 'log_sha256' in entry:ok(entry['log_sha256']==c['log_sha256'],'contemporaneous log binding '+module)
 else:ok(module=='NLA.MI04.Quadratic','only disclosed direct Quadratic log field absent')
 rel='Solution.lean' if module.endswith('.Complete') else module.replace('.','/')+'.lean'
 ok(c['source_sha256']==S[rel] and c['exit_code']==0,'exact source actual exit0 '+module)
 origin.append({'module':module,'receipt':str(recpath.relative_to(P)),'source_sha256':c['source_sha256'],'exit_code':c['exit_code'],'contemporaneous_log_hash': 'log_sha256' in entry})
config=read(P/'comparator.json');names=config['theorem_names'];ok(len(names)==21 and len(set(names))==21,'exact distinct 21 Comparator targets')
ok(config['definition_names']==[] and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'},'no replaceable definition holes or extra permitted axioms')
meta=yaml.safe_load(bind(P/'formalization.yaml').read_text());rows=meta['status']['main_results'];ok([r['declaration'] for r in rows]==names,'all advertised results selected exactly once')
complete=(P/pm[A['actual_commands']['NLA.MI04.Complete']['log']]['path']).read_text()
observed={n:xs.split(', ') for n,xs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",complete)}
ok(observed==A['observed_axioms'] and set(observed)==set(names),'actual Complete log gives all 21 expected standard axiom lists')
texts={rel:(P/rel).read_text() for rel in S}
for rel,t in texts.items():
 ok(not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^\s*axiom\s',t,re.M),'active source has no holes/custom axioms/native trust '+rel)
 for imp in re.findall(r'^import\s+([^\n]+)',t,re.M):
  for mod in imp.split():
   ok(mod!='Challenge','no Challenge implementation import '+rel)
   if mod.startswith('NLA.MI04.'):ok(mod.replace('.','/')+'.lean' in S,'full local import closure '+mod)
for name in names:ok('#assert_trust kernel '+name.rsplit('.',1)[1] in texts['Solution.lean'],'Solution consumes kernel assertion '+name)
def decl(t,n):
 h=list(re.finditer(r'^\s*(?:theorem|lemma)\s+'+re.escape(n)+r'\b[\s\S]*?\s:=',t,re.M));ok(len(h)==1,'unique actual declaration '+n);x=h[0];off=x.start()+len(x.group())-len(x.group().lstrip());return hashlib.sha256(x.group().strip().encode()).hexdigest(),t.count('\n',0,off)+1
im=read(P/'IMPLEMENTATION-MAP.json')
for row,r in zip(rows,im['export_locations']):
 name=row['declaration'];ok(row['file']==r['path'] and row['file_sha256']==r['file_sha256']==S[r['path']],'metadata actual file identity '+name)
 h,line=decl(texts[r['path']],name.rsplit('.',1)[1]);ok(h==r['implementation_header_sha256'] and line==r['line']==row['line'],'implementation header and line '+name)
 h,line=decl((P/'Challenge.lean').read_text(),name.rsplit('.',1)[1]);ok(h==r['challenge_header_sha256'] and line==r['challenge_line'],'frozen header and line '+name)
 ok(set(row['axioms'])=={'propext','Classical.choice','Quot.sound'} and 'pending' in row['verification_status'].lower(),'honest per-export local/canonical status '+name)
ok(A['canonical_verification_completed']==False and A['comparator_run']==False and A['count_change']==0,'local acceptance makes no canonical or count claim')
PE=read(P/'PUBLICATION-EVIDENCE.json');ok(PE['canonical_verification_completed']==False and PE['canonical_run_id'] is None and PE['published_commit'] is None,'publication metadata does not invent run or commit')
email=re.compile(rb'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
for rel in actual:ok(email.search((P/rel).read_bytes()) is None,'no contact bytes '+rel)
for row in read(P/'verification/OMITTED-ORIGINALS.json')['privacy_omissions']:
 path=row['original_path'];ok(not(P/path).exists(),'contact-bearing wrapper omitted '+path)
 original=B/'inequalities/MI-04'/path;bind(original,row['sha256']);ok(email.search(original.read_bytes()) is not None,'omission accurately identifies contact-bearing wrapper '+path)
 rel=path.removeprefix('source/');raw=subprocess.check_output(['git','-C',str(I),'show','ce47b5630bf3680d9211131c3a43825b022c139a:'+rel],env={**os.environ,'GIT_OPTIONAL_LOCKS':'0'})
 ok(hashlib.sha256(raw).hexdigest()==row['sha256'],'omitted wrapper has exact immutable original Git blob '+path)
for row in read(P/'reviews/INDEX.json')['reports']:bind(P/row['path'],row['sha256'])
validator=bind(I/'tools/lean/validate_manifest.py');schema=bind(I/'docs/lean/schema/v0.4.schema.json');bind(P/'verification/packaging/v0.4.schema.json',sha(schema))
proc=subprocess.run([sys.executable,str(validator),str(P)],text=True,capture_output=True)
(O/'schema-validation.log').write_text(proc.stdout+proc.stderr);ok(proc.returncode==0,'actual independently invoked schema and exact Comparator coverage validator exit0')
# Recheck sealed input closure after this wholly read-only audit.
for rel,h in manifest['files'].items():bind(P/rel,h)
result={'reviewer':'/root/mf22_publication_referee','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'bounded independent MI04 canonical package continuation; no Lean or canonical runtime execution','package_file_count':len(actual),'source_count':len(S),'export_count':len(names),'retained_original_count':206,'checks':checks,'bindings':bindings,'actual_local_origins':origin,'schema_command':[sys.executable,str(validator),str(P)],'schema_exit_code':proc.returncode,'canonical_verification_completed':False,'count_change':0,'limitations':A['limitations']}
(O/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'pass':True,'checks':len(checks),'bindings':len(bindings),'files':len(actual),'sources':len(S),'exports':len(names),'schema_exit':proc.returncode}))
