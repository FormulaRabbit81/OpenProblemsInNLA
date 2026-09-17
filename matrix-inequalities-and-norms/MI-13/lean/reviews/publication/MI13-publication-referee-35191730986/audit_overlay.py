"""Independent publication-overlay correspondence audit; no Git/compiler/network."""
from pathlib import Path
import hashlib, json, re, sys
import yaml, jsonschema
B=Path('/private/tmp/nla-lean-next-20260915')
O=B/'MI13-publication-private-35191730986'
W=Path('/private/tmp/nla-lean-next-mi13-worktree')
R=B/'reviews/MI13-publication-referee-35191730986'
LREL='matrix-inequalities-and-norms/MI-13/lean'
QREL='matrix-inequalities-and-norms/MI-13'
E=O/'overlay'/LREL/'verification/linux-35191730986'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
j=lambda p:json.loads(Path(p).read_text())
checks=[];bindings={}
def ck(name,a,b=True):
 checks.append({'name':name,'passed':a==b})
 assert a==b,(name,a,b)
def bind(p):bindings[str(p)]=sha(p)
ck('expected sealed overlay manifest',sha(O/'MANIFEST.json'),'4e2df1f49543730fb01d2e64181fb84cf26a59cf4c15c92f613e9f7b9859fcd3')
for rel,digest in j(O/'MANIFEST.json')['files'].items():
 ck('overlay packet hash '+rel,sha(O/rel),digest);bind(O/rel)
bind(O/'MANIFEST.json')
t=j(O/'TRANSITION.json');run=j(E/'result.json');audit=j(E/'ROOT-AUDIT.json')
ck('exact proof commit',t['proof_commit'],'e37310121f154b1a0d94efa4f98fdcd469177134')
ck('literal run source commit',run['repository_commit'],t['proof_commit'])
ck('root audit source commit',audit['actual_checkout'],t['proof_commit'])
ck('root audit digest',sha(E/'ROOT-AUDIT.json'),'f25243365af6e0060f3af57dcb0a6a62ca3933b82fa52067d7046ca02f201fb7')
ck('bound input count in actual result',len(run['input_sha256']),1183)
ck('overlay path count',len(t['overlay']),30)
ck('protected path count',len(t['protected_original_inputs']),31)
ck('no ID registry or unrelated mathematical target changed',all(p=='RESOLVED.md' or p.startswith(QREL+'/') for p in t['overlay']))
ck('no active mathematical/config input changed by overlay',not any(LREL+'/'+p in t['overlay'] for p in t['protected_original_inputs']))
for rel,digest in t['overlay'].items():ck('transition overlay hash '+rel,sha(O/'overlay'/rel),digest)
for rel,digest in t['before'].items():
 if digest is not None:
  ck('transition before hash '+rel,sha(O/'before'/rel),digest)
  ck('actual current protected predecessor '+rel,sha(W/rel),digest);bind(W/rel)
for rel,digest in t['protected_original_inputs'].items():
 ck('protected source matches actual current source '+rel,sha(W/LREL/rel),digest)
 ck('protected source is exact Linux input '+rel,run['input_sha256'][rel],digest)
 bind(W/LREL/rel)
ck('23 active Lean inputs including Challenge',sum(p.endswith('.lean') for p in t['protected_original_inputs']),23)
old=(O/'before'/QREL/'README.md').read_text();new=(O/'overlay'/QREL/'README.md').read_text()
for start,end in [('## Problem statement','## Relevance'),('## Resolution proof','## Status evidence')]:
 before=old.split(start,1)[1].split(end,1)[0]
 after=new.split(start,1)[1].split(end,1)[0].split('## Lean proof and verification evidence',1)[0]
 ck('exact original mathematical section retained '+start,before,after)
ck('literature date unchanged','**Last checked:** 2026-09-10' in new)
ck('formalization date distinct','## Lean proof and verification evidence — 2026-09-17' in new)
oldr=(O/'before/RESOLVED.md').read_text();newr=(O/'overlay/RESOLVED.md').read_text()
def splitentry(s):
 a=s.index('### ✅ MI-13');b=s.index('\n### ',a+1);return s[:a],s[a:b],s[b:]
a,entry,b=splitentry(oldr);aa,newentry,bb=splitentry(newr)
ck('resolved index preceding entries unchanged',a,aa);ck('resolved index following entries unchanged',b,bb)
for label,s in [('canonical page',new),('resolved entry',newentry),('Lean README',(O/'overlay'/LREL/'README.md').read_text()),('PR body',(O/'PR-BODY.md').read_text())]:
 ck('George attribution '+label,'George Stepaniants' in s)
 ck('department attribution '+label,'Department of Computing and Mathematical Sciences' in s)
 ck('university attribution '+label,'California Institute of Technology' in s)
ck('original Nobori attribution retained','Nobori' in new)
ck('original Audenaert attribution retained','Audenaert' in new)
ck('no novel informal-proof authorship assigned','repository contributors for the informal reduction' in new)
email=re.compile(rb'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
ck('no email strings in publication overlay',not any(email.search((O/'overlay'/p).read_bytes()) for p in t['overlay']))
# Parse the actual formalization metadata and validate every declaration-to-source mapping.
meta_path=O/'overlay'/LREL/'formalization.yaml';meta=yaml.safe_load(meta_path.read_text())
schema_path=W/'docs/lean/schema/v0.4.schema.json';schema=j(schema_path)
jsonschema.validate(meta,schema);ck('formalization.yaml actual pinned schema validation',True);bind(schema_path)
config=j(W/LREL/'comparator.json');ck('literal current Comparator config matches actual run',config,run['config'])
names=config['theorem_names'];entries=meta['status']['main_results']
ck('36 metadata declarations',len(entries),36)
ck('metadata order and coverage equal literal Comparator contracts',[e['declaration'] for e in entries],names)
ck('all theorem names distinct',len(set(names)),36)
ck('no replaceable definitions',config['definition_names'],[])
ck('exact standard permitted-axiom set',set(config['permitted_axioms']),{'propext','Quot.sound','Classical.choice'})
log=(E/'comparator.log').read_text()
for entry in entries:
 name=entry['declaration'];src=W/LREL/entry['file'];lines=src.read_text().splitlines()
 ck('metadata source hash '+name,sha(src),entry['file_sha256'])
 ck('metadata source included in actual execution '+name,run['input_sha256'][entry['file']],entry['file_sha256'])
 ck('metadata declaration line '+name,bool(re.search(r'\btheorem\s+'+re.escape(name.split('.')[-1])+r'\b',lines[entry['line']-1])))
 ck('metadata says exact source revision '+name,t['proof_commit'] in entry['verification_status'])
 ck('metadata says exact run '+name,'35191730986' in entry['verification_status'])
 ck('metadata has zero implementation holes '+name,entry['sorry_count'],0)
 ck('metadata permitted axiom set '+name,set(entry['axioms']),{'propext','Quot.sound','Classical.choice'})
 matches=re.findall(r"info: Solution\.lean:\d+:\d+: '"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]",log)
 ck('actual Solution axiom report uniquely present '+name,len(matches),1)
 ck('actual Solution axiom report '+name,{x.strip() for x in matches[0].split(',')},{'propext','Quot.sound','Classical.choice'})
ck('actual Comparator final success','Lean default kernel accepts the solution\nYour solution is okay!' in log and log.rstrip().endswith('EXIT_STATUS=0'))
ck('all 36 root audit exports same contracts',audit['exports'],names)
ck('honest metadata proof-vs-semantic separation',run['semantic_review'],'not-performed-by-this-command')
for f,digest in audit['raw_logs_sha256'].items():ck('raw runtime log bound '+f,sha(E/f),digest)
for f,markers in {
 'kernel-controls.log':['PASS: all three actual Comparator.runBuiltinKernel cases behaved as required','Lean default kernel rejects the solution','Quotient post-check rejects the solution'],
 'comparator-controls.log':['PASS: all five Comparator regressions'],
 'negative-sorry.log':["Illegal axiom detected: 'sorryAx'",'EXIT_STATUS=1'],
 'negative-native.log':["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'",'EXIT_STATUS=1'],
 'sandbox.log':['MODE build: exit=0','MODE export: exit=0','Sandbox UID: 1001','PASS AF_UNIX socket creation: denied','Outer and export fixture contents unchanged']}.items():
 raw=(E/f).read_text()
 for marker in markers:ck('documented control result '+f+' '+marker,marker in raw)
state=j(O/'overlay'/LREL/'STATE.json');pub=j(O/'overlay'/LREL/'PUBLICATION-EVIDENCE.json')
ck('publication not yet claimed',state['published'],False);ck('count not yet changed',state['count_change'],0)
ck('runtime review remains pending in original overlay',pub['independent_runtime_review'],'pending')
ck('publication review remains pending in original overlay',pub['publication_review'],'pending')
ck('all original source-stage metadata preserved',all((O/'overlay'/LREL/'verification/publication-before'/n).read_bytes()==(O/'before'/LREL/n).read_bytes() for n in ['README.md','formalization.yaml','STATE.json']))
# Local links in changed human-facing Markdown are checked against the hybrid view.
for rel in [QREL+'/README.md',LREL+'/README.md']:
 s=(O/'overlay'/rel).read_text()
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if target.startswith(('http:','https:','#')):continue
  path=target.split('#',1)[0]
  if not path:continue
  base=(Path(rel).parent/path)
  exists=(O/'overlay'/base).exists() or (W/base).exists()
  ck('local publication link '+rel+' '+target,exists)
(R/'CHECKS.json').write_text(json.dumps({'scope':'Independent nonauthor publication-overlay source/evidence correspondence audit. This did not execute Lean, LeanCert, Comparator, Git, network or publication. It authenticates the 31 protected inputs against actual run bindings; separate runtime referee audits all 1183 inputs.','checks':checks,'all_passed':all(c['passed'] for c in checks)},indent=2)+'\n')
(R/'BINDINGS.json').write_text(json.dumps({'files':bindings},indent=2)+'\n')
print(json.dumps({'checks':len(checks),'all_passed':all(c['passed'] for c in checks),'protected_inputs':31,'active_Lean_inputs':23,'exact_contracts':36,'overlay_paths':30,'metadata_schema':'passed'}))
