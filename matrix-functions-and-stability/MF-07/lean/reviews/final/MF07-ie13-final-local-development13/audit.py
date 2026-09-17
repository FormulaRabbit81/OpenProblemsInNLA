from pathlib import Path
import datetime,hashlib,json,re,subprocess
B=Path('/tmp/nla-lean-next-20260915');L=Path('/private/tmp/nla-lean-local-shared-20260916');W=B/'next-statements/MF-07';O=Path(__file__).parent
bindings={};cache={}
def sha(p):
 p=Path(p)
 if str(p) not in cache:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for x in iter(lambda:f.read(1024*1024),b''):h.update(x)
  cache[str(p)]=h.hexdigest()
 bindings[str(p)]=cache[str(p)];return cache[str(p)]
def read(p):sha(p);return Path(p).read_text()
def js(p):return json.loads(read(p))
a=js(B/'MF07-LOCAL-DEVELOPMENT-ACCEPTANCE.json');rpath=Path(a['receipt']);r=js(rpath);assembly=js(L/'ASSEMBLY-13.json');env=js(L/'LOCAL-ENVIRONMENT.json')
assert sha(rpath)==a['receipt_sha256'] and sha(L/'ASSEMBLY-13.json')==a['assembly_sha256']==r['assembly_sha256']
assert sha(L/'serial_compile_v3.py')==r['runner_sha256']
assert sha(env['compiler'])==r['compiler_sha256']==a['compiler_sha256']
assert sha(B/'audit_mf07_local_development13.py')==a['audit_script_sha256']
assert r['end'] and r['platform']=='darwin' and r['max_compiler_processes']==r['threads']==1
assert r['source_inputs']=={p:v['sha256'] for p,v in assembly['sources'].items()}
assert not any(m.startswith('NLA.MF07.') for m in r['failed_modules']+r['blocked_modules'])
sources={p:v for p,v in assembly['sources'].items() if p.startswith('NLA/MF07/')};assert len(sources)==21
canonical={('Solution.lean' if p.endswith('/Complete.lean') else p):v['sha256'] for p,v in sources.items()};assert canonical==a['accepted_source_sha256']
texts={}; mods={}
for p,v in sources.items():
 assert sha(L/p)==sha(v['source'])==v['sha256']==r['source_inputs'][p],p
 texts[p]=read(v['source']);mods[p[:-5].replace('/','.')]=p
imports={m:[x for line in texts[p].splitlines() if line.startswith('import ') for x in line[7:].split() if x.startswith('NLA.')] for m,p in mods.items()}
closures={}
def closure(m,seen=()):
 assert m not in seen
 if m not in closures:closures[m]={m}|set().union(*(closure(x,seen+(m,)) for x in imports[m]))
 return closures[m]
assert closure('NLA.MF07.Complete')==set(mods)
assert all('import Challenge' not in t for t in texts.values())
outputs={m:sha(L/'.lake/build/lib/lean'/(p[:-5]+'.olean')) for m,p in mods.items()}
receipts={str(p):js(p) for p in sorted((L/'runs').glob('development-*/RECEIPT.json')) if p.name=='RECEIPT.json'}
origins={};ancestry={}
def verify(c,path,m,seen=()):
 key=(str(path),m);assert key not in seen
 assert c['source_sha256']==sources[mods[m]]['sha256'] and c['output_sha256']==outputs[m]
 if c.get('status')=='reused_exact_successful_local_output':
  if 'prior_command' in c:
   matches=[(Path(p),v) for p,j in receipts.items() if j.get('end') for v in j['commands'] if v==c['prior_command']]
   assert matches,(m,'missing original embedded command')
   p,nxt=matches[0]
  else:
   p=Path(c['prior_receipt']);assert sha(p)==c['prior_receipt_sha256'];j=receipts[str(p)];assert j.get('end')
   assert c['transitive_source_hashes']=={mods[d]:sources[mods[d]]['sha256'] for d in closure(m)}
   for d in closure(m):
    h=j['source_inputs'][mods[d]];assert (h['sha256'] if isinstance(h,dict) else h)==sources[mods[d]]['sha256']
   matches=[v for v in j['commands'] if v.get('module')==m and v.get('source_sha256')==c['source_sha256'] and v.get('output_sha256')==c['output_sha256']]
   assert len(matches)==1;nxt=matches[0]
  ancestry.setdefault(m,[]).append({'receipt':str(path),'sha256':sha(path),'prior':str(p),'prior_sha256':sha(p)})
  return verify(nxt,p,m,seen+(key,))
 assert c['exit_code']==0 and c['end'] and c['argv'][0]==env['compiler']
 assert '--threads=1' in c['argv'] and ('--memory=4096' in c['argv'] or '--memory=3072' in c['argv'])
 log=path.parent/(m+'.log');assert sha(log)==c['log_sha256'];t=read(log)
 assert not re.search(r'(^|\n).*error(?:\(|:)',t) and 'sorryAx' not in t and 'declaration uses `sorry`' not in t
 for d,h in c.get('dependency_olean_sha256',{}).items():assert h==outputs[d]
 actual={'receipt':str(path),'receipt_sha256':sha(path),'log':str(log),'log_sha256':sha(log),'exit_code':0,'source_sha256':c['source_sha256'],'output_sha256':c['output_sha256'],'argv':c['argv']}
 assert actual==a['actual_commands'][m]
 return actual
commands={c['module']:c for c in r['commands'] if c['module'] in mods};assert set(commands)==set(mods)
for m,c in commands.items():origins[m]=verify(c,rpath,m)
fresh=[m for m,c in commands.items() if c.get('exit_code')==0];reused=[m for m,c in commands.items() if c.get('status')=='reused_exact_successful_local_output']
assert len(fresh)==4 and len(reused)==17
freeze=js(W/'STATEMENT-FREEZE.json');frozen=freeze['frozen_files_sha256'];assert frozen==a['frozen_files_sha256'] and len(frozen)==10
for p,h in frozen.items():assert sha(W/p)==sha(W/freeze['snapshot_directory']/p)==h
config=js(W/'comparator.json');names=config['theorem_names'];assert len(names)==18 and config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
complete=texts['NLA/MF07/Complete.lean']; assert re.findall(r'^#print axioms (\S+)',complete,re.M)==names
assert re.findall(r'^#assert_trust kernel (\S+)',complete,re.M)==names
ct=read(Path(origins['NLA.MF07.Complete']['log']))
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",ct)
assert [n for n,_ in reports]==names and all(set(v.split(', '))==set(config['permitted_axioms']) for _,v in reports)
challenge=read(W/'Challenge.lean');headers={};normalize=lambda x:re.sub(r'\s+','',x)
for fq in names:
 n=fq.rsplit('.',1)[1];pat=r'(?m)^theorem '+re.escape(n)+r'\b(.*?):= by'
 ch=re.search(pat,challenge,re.S).group(1)
 pairs=[(p,m.group(1)) for p,t in texts.items() for m in [re.search(pat,t,re.S)] if m];assert len(pairs)==1
 p,impl=pairs[0];a1=normalize(ch);a2=normalize(impl)
 normalization='whitespace only'
 if n=='radius_one_semantics':a1=a1.replace('Filter.','');normalization='explicit Filter namespace versus open Filter'
 if n=='rounded_extremal_norm':
  a2=a2.replace('∃(Q:Squared)(σ:Find→ℝ)(w:EuclideanVectord→ℝ),','∃Q:Squared,∃σ:Find→ℝ,∃w:EuclideanVectord→ℝ,');normalization='successive versus grouped identical existential binders'
 assert a1==a2,n
 headers[n]={'path':p,'normalization':normalization,'Challenge':ch.strip(),'implementation':impl.strip()}
for p,t in texts.items():
 code=re.sub(r'/\-[\s\S]*?\-/','',t);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe)\b',code),p
 assert not re.search(r'^\s*(?:variable|axiom)\b',code,re.M),p
assert 'interval_decide (trust := kernel)' in texts['NLA/MF07/Numerical.lean']
assert 'exp_one_bound m' in texts['NLA/MF07/Numerical.lean'] and 'comparison_threshold_bound' in texts['NLA/MF07/Final.lean']
pins={v['name']:v['rev'] for v in js(W/'lake-manifest.json')['packages']};assert pins==a['dependency_commits']
for dep,h in pins.items():
 p=L/'.lake/packages'/dep
 assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==h
 assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],text=True)
prov=js(W/'SOURCE-PROVENANCE.json');repo=Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
for s in prov['sources'][:2]:
 assert sha(W/s['packet_path'])==s['sha256']
 data=subprocess.check_output(['git','-C',str(repo),'show',s['commit']+':'+s['path']]);assert hashlib.sha256(data).hexdigest()==s['sha256']
apiroot=L/'.lake/packages/mathlib'
for rel in ['Analysis/Subadditive.lean','Analysis/InnerProductSpace/Spectrum.lean','LinearAlgebra/Matrix/Determinant/Basic.lean','Analysis/CStarAlgebra/Matrix.lean','Analysis/CStarAlgebra/Basic.lean']:
 p=apiroot/'Mathlib'/rel
 actual=subprocess.check_output(['git','-C',str(apiroot),'show',pins['mathlib']+':Mathlib/'+rel]);assert hashlib.sha256(actual).hexdigest()==sha(p)
for name in ['correctness.md','generality.md','proof-quality.md','reuse.md','attribution.md']:sha(W/'sources/standards/TauCetiProject/TauCetiReview/rubrics'/name)
for d in sorted((B/'reviews').glob('MF07-ie13*')):
 if d==O:continue
 for p in ['MANIFEST.json','REVIEW.md']:
  if (d/p).exists():sha(d/p)
repair=B/'local-routine-repairs/development11'
for p in ['MANIFEST.json','CHECKS.json','PLAN.json','NLA.MF07.Similarity.log','before/NLA/MF07/Similarity.lean.txt','after/NLA/MF07/Similarity.lean.txt']:
 f=repair/p
 if f.exists():sha(f)
checks={'reviewer':'/root/ie13_continuation','role':'Full independent nonauthor proof-source review and source-bound local evidence audit; earlier statement-draft author, not an independent reviewer of own original statement design',
 'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'APPROVED full proof-source candidate and local development evidence; canonical Linux pending',
 'all21_Lean_files_read':True,'total_Lean_lines':sum(len(t.splitlines()) for t in texts.values()),'all18_Challenge_contracts_and_full_original_manuscript_read':True,
 'all_recorded_source_inputs_match_assembly':len(r['source_inputs']),'current_MF07_sources_outputs':21,'actual_fresh_MF07_modules':fresh,'exact_reused_MF07_modules':reused,
 'all21_origin_logs_read':True,'all21_actual_origin_commands_exit_zero':True,'actual_complete_exports':names,'all_export_axioms':a['observed_axioms'],
 'frozen_files_unchanged':10,'public_header_matches':{'whitespace_only':16,'Filter_namespace':1,'grouped_existentials':1},'pins':pins,
 'local_run_terminal':r['end'],'overall_run_failures_other_projects_only':r['failed_modules'],'overall_run_blocked_other_projects_only':r['blocked_modules'],
 'source_map':canonical,'source_import_closure_all21_no_Challenge':True,'routine_Similarity_repair':'Only explicit real-to-complex inverse equality, same existing statement; actual source and passed retry reviewed',
 'LeanCert_consumed':'Kernel exp(1)<=3 certificate -> variable_binomial_bound -> comparison_threshold_bound -> radius_one_growth -> canonical_uniform_bound',
 'numeric_computation_scope':'One exact argument 1; all dimensions, lengths, thresholds and powers symbolic; orbit norm avoids 2^n term enumeration',
 'scope_limits':['No Lean/Lake/cache/compiler invocation by this reviewer.','Actual local executions were on macOS using shared pinned compiled dependencies; no Linux Comparator/default-kernel replay/controls by this audit.','The whole shared run has other-project failures; all MF07 modules passed or are exact source-bound reuses.','No publication commit or upstream PR accepted; no count change.'],
 'count_change':0}
(O/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
(O/'SOURCE-BINDINGS.json').write_text(json.dumps(bindings,indent=2,sort_keys=True)+'\n')
(O/'CONTRACT-COMPARISON.json').write_text(json.dumps(headers,indent=2,ensure_ascii=False)+'\n')
(O/'RUNTIME-ORIGINS.json').write_text(json.dumps({'origins':origins,'reuse_ancestry':ancestry},indent=2)+'\n')
print(json.dumps({'pass':True,'bindings':len(bindings),'sources':len(texts),'lines':checks['total_Lean_lines'],'fresh':len(fresh),'reused':len(reused),'public_contracts':len(headers)}))
