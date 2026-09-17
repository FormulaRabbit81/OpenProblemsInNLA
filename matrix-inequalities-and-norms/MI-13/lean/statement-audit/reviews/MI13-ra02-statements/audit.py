"""Read-only independent MI-13 statement audit. No Lean, Lake, Git, cache or network execution."""
from pathlib import Path
import datetime, hashlib, json, re
B = Path('/tmp/nla-lean-next-20260915')
P = B / 'next-statements/MI-13'
OUT = B / 'reviews/MI13-ra02-statements'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
checks, bindings = [], {}
def check(label, value):
    checks.append({'check':label, 'pass':bool(value)})
    if not value: raise AssertionError(label)
def bind(p, h=None):
    p = Path(p); actual = sha(p)
    if h is not None: check('digest ' + str(p), h == actual)
    bindings[str(p)] = actual
    return p
def read(p, h=None): return json.loads(bind(p,h).read_text())
def strip_comments(t):
    out, i, depth = [], 0, 0
    while i<len(t):
        if t[i:i+2]=='/-': depth+=1; i+=2
        elif depth and t[i:i+2]=='-/': depth-=1; i+=2
        elif depth:
            if t[i]=='\n': out.append('\n')
            i+=1
        elif t[i:i+2]=='--':
            j=t.find('\n',i);i=len(t) if j<0 else j
        else:out.append(t[i]);i+=1
    check('balanced comments',depth==0)
    return ''.join(out)
man = read(P/'DRAFT-MANIFEST.json','388c3556730a9fc132ac7cd2f72493b468f233d6e683dba74d69b9d40fd972c7')
for rel,h in man['files'].items(): bind(P/rel,h)
check('all 54 inventoried files match',len(man['files'])==54)
check('manifest exactly inventories packet',set(man['files'])=={str(f.relative_to(P)) for f in P.rglob('*') if f.is_file() and f.name!='DRAFT-MANIFEST.json'})
check('only two active Lean files',sorted(str(f.relative_to(P)) for f in P.rglob('*.lean'))==['Challenge.lean','NLA/MI13/Definitions.lean'])
d = strip_comments((P/'NLA/MI13/Definitions.lean').read_text())
c = strip_comments((P/'Challenge.lean').read_text())
check('exact Definitions hash',sha(P/'NLA/MI13/Definitions.lean')=='add61115ca2d92951bfc479c3de4dcbb9f2b850cac2ab793cf0dcf543e75622b')
check('exact Challenge hash',sha(P/'Challenge.lean')=='6fc6f34a1a559097379921a8237c1b23ea15c67ff7bf23b7ffd60ff3d107f088')
check('no definition hole or custom trust extension',not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|elab|macro|initialize|extern|implemented_by)\b',d))
check('only genuine external definition dependencies',all(x.startswith('Mathlib.') for x in re.findall(r'^import (\S+)$',d,re.M)))
check('Challenge only imports shared Definitions',re.findall(r'^import (\S+)$',c,re.M)==['NLA.MI13.Definitions'])
check('no proof or Solution or freeze file',not (P/'Solution.lean').exists() and not (P/'STATEMENT-FREEZE.json').exists())
check('explicit implicit-variable policy',all('set_option autoImplicit false' in x for x in [d,c]))
check('no custom trust/instance alterations',not re.search(r'^\s*(?:axiom|instance|local instance|attribute|elab|macro|initialize)\b',d+'\n'+c,re.M))
check('36 explicit Challenge placeholders',len(re.findall(r'\bsorry\b',c))==36)
matches=list(re.finditer(r'\btheorem\s+(\w+)\s*(.*?)\s*:=\s*by\s*\n\s*sorry',c,re.S))
check('36 theorem statements and no proof bodies',len(matches)==36 and len(re.findall(r'^theorem ',c,re.M))==36)
headers={'NLA.MI13.'+m.group(1):m.group(0).rsplit(':=',1)[0].rstrip() for m in matches}
config=read(P/'comparator.json');records=read(P/'STATEMENT-HEADERS.json')['declarations']
check('all36 configured exactly once',len(config['theorem_names'])==36 and set(config['theorem_names'])==set(headers))
check('no proposed definition hole and only standard axioms',config['definition_names']==[] and set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
check('separate configured challenge and solution',config['challenge_module']=='Challenge' and config['solution_module']=='Solution')
check('36 stored exact headers',len(records)==36 and {r['name'] for r in records}==set(headers))
for r in records:
    check('header '+r['name'],headers[r['name']]==r['header'])
    check('header digest '+r['name'],hashlib.sha256(r['header'].encode()).hexdigest()==r['header_sha256'])
    check('header line '+r['name'],(P/'Challenge.lean').read_text().splitlines()[r['line']-1].startswith('theorem '+r['name'].split('.')[-1]))
num=read(P/'NUMERICAL-FIRST.json','1676285e543d2cf9e1d9d01bc8767109b87c68fc86adc8ab91990a659b001f12')
for rel,h in num['files'].items():bind(P/rel,h)
state=read(P/'STATE.json')
check('recorded numerical plan precedes recorded draft stage',num['recorded_at_utc']<state['created_at_utc'])
check('draft status declines all runtime/freeze/publication claims',all(state[k] is False for k in ['proof_implementation','local_Lean_Lake_or_cache_invocation','LeanCert_executed','Comparator_executed','statement_freeze','canonical_verified','Git_mutation','published']))
check('no count change',state['count_change']==0)
prov=read(P/'SOURCE-PROVENANCE.json');reuse=read(P/'REUSE-AUDIT.json')
bind(prov['canonical']['source'],prov['canonical']['sha256'])
for r in prov['reference_copies']:bind(P/r['packet_path'],r['sha256'])
for group in ['standards','patterns','primary']:
    for r in reuse[group]:bind(r['source'],r['sha256']);bind(P/r['packet_path'],r['sha256'])
for key in ['informal_route_manifest','informal_referee_manifest']:
    bind(prov[key]['path'],prov[key]['sha256'])
pins={q['name']:q['rev'] for q in read(P/'lake-manifest.json')['packages']}
check('all 10 dependency pins match reuse audit',pins=={q['name']:q['revision'] for q in reuse['dependency_pin_checks']})
check('required primary pins',pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926')
check('no global Nonempty or Nontrivial helper restriction',not re.search(r'\b(?:variable|instance|letI)\b.*\b(?:Nonempty|Nontrivial)\b',d+'\n'+c))
check('norms explicitly use Euclidean maps/entries',
      'spectralNorm {m n : ℕ} (A : Rect m n) : ℝ := ‖euclideanCLM A‖' in d and
      'frobeniusNorm {m n : ℕ} (A : Rect m n) : ℝ := ‖flatten A‖' in d and
      '(euclideanLin A).singularValues k' in d)
canonical=headers['NLA.MI13.canonical_rectangular_bound']
check('literal final rectangular target without extra hypotheses',
      canonical=='''theorem canonical_rectangular_bound {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (A C : Rect m n) (B : Rect n m) :
    frobeniusNorm (A * B * C - C * B * A) ^ 2 ≤
      2 * spectralNorm B ^ 2 * (singularValue A 0 ^ 2 + singularValue A 1 ^ 2) *
        frobeniusNorm C ^ 2''')
formal=(P/'formalization.yaml').read_text()
check('metadata has no claimed main result', '  main_results: []' in formal)
check('metadata names authorized contributor and department','George Stepaniants' in formal and 'Department of Computing and Mathematical Sciences' in formal and 'Institute of Technology' in formal)
check('no email in packet',not any(re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',(P/rel).read_text()) for rel in man['files']))
result={'reviewer':'/root/ra02_full_final_referee','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Independent nonauthor statement/source review and static digest/header audit; not proof or runtime approval',
 'definitions_lines_read':len((P/'NLA/MI13/Definitions.lean').read_text().splitlines()),
 'challenge_lines_read':len((P/'Challenge.lean').read_text().splitlines()),
 'canonical_lines_read':len((P/'sources/canonical/README.md').read_text().splitlines()),
 'contract_count':len(headers),'checks':checks,'check_count':len(checks),'bindings':bindings,'binding_count':len(bindings),
 'all_checks_passed':all(x['pass'] for x in checks),'new_Lean_Lake_Git_cache_or_network_run':False,
 'statement_freeze':False,'proof_approval':False,'Comparator_run':False,'LeanCert_run':False,'count_change':0}
(OUT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'HEADERS.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['definitions_lines_read','challenge_lines_read','canonical_lines_read','contract_count','check_count','binding_count','all_checks_passed']}))
