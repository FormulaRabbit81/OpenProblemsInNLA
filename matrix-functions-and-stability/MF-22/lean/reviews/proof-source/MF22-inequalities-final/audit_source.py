from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).parent
S=R/'snapshot'
A=Path('/tmp/nla-lean-next-20260915/matrix-functions/MF-22')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(t):
    out=[];i=0;depth=0
    while i<len(t):
        if t[i:i+2]=='/-':depth+=1;i+=2;continue
        if depth and t[i:i+2]=='-/':depth-=1;i+=2;continue
        if depth:i+=1;continue
        if t[i:i+2]=='--':
            j=t.find('\n',i);i=len(t) if j<0 else j;continue
        out.append(t[i]);i+=1
    assert depth==0
    return ''.join(out)
inputs=json.loads((R/'INPUTS.json').read_text())
assert all(sha(S/p)==h for p,h in inputs.items())
manifest=json.loads((S/'development-handoffs/repair-35043317938/INTEGRATED-MANIFEST.json').read_text())
proof=manifest['complete_current_proof_closure']
assert len(proof)==29
assert all(sha(S/p)==sha(A/p)==h for p,h in proof.items())
frozen=json.loads((S/'STATEMENT-FREEZE.json').read_text())
assert len(frozen['frozen_files_sha256'])==10
assert all(sha(S/p)==sha(A/p)==h for p,h in frozen['frozen_files_sha256'].items())
assert all(sha(S/d['retained_path'])==d['sha256'] for d in frozen['reviews'])
texts={p:strip_comments((S/p).read_text()) for p in proof}
forbidden={p:re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|elab|run_tac)\b',t) for p,t in texts.items()}
assert not any(forbidden.values()),forbidden
modules={p[:-5].replace('/','.') : p for p in proof}
graph={p:[] for p in proof}
external=set()
for p,t in texts.items():
    for line in re.findall(r'^import\s+(.+)$',t,re.M):
        for mod in line.split():
            assert mod!='Challenge'
            if mod in modules:graph[p].append(modules[mod])
            else:
                assert not mod.startswith('NLA.MF22.'),(p,mod)
                external.add(mod)
seen=set()
def visit(p):
    if p in seen:return
    seen.add(p)
    for q in graph[p]:visit(q)
visit('Solution.lean')
assert seen==set(proof),sorted(set(proof)-seen)
challenge=strip_comments((S/'Challenge.lean').read_text())
ct=dict(re.findall(r'\btheorem\s+(\w+)\s+(.*?)\s*:=\s*by',challenge,re.S))
assert len(ct)==22 and len(re.findall(r'\bsorry\b',challenge))==22
all_decl={}
for p,t in texts.items():
    for name,ty in re.findall(r'\b(?:theorem|lemma)\s+(\w+)\s+(.*?)\s*:=\s*by',t,re.S):
        assert name not in all_decl,name
        all_decl[name]=(p,ty)
normalize=lambda s: re.sub(r'\s+','',s)
sigchecks=[]
for name,ty in ct.items():
    assert name in all_decl,name
    p,actual=all_decl[name]
    equal=normalize(ty)==normalize(actual)
    sigchecks.append({'name':name,'source':p,'whitespace_normalized_signature_equal':equal})
assert all(x['whitespace_normalized_signature_equal'] for x in sigchecks),sigchecks
comp=json.loads((S/'comparator.json').read_text())
assert comp['theorem_names']==['NLA.MF22.'+n for n in ct]
assert comp['definition_names']==[]
assert comp['permitted_axioms']==['propext','Classical.choice','Quot.sound']
solution=texts['Solution.lean']
for n in ct:
    assert '#assert_trust kernel '+n in solution and '#print axioms '+n in solution
pins=json.loads((S/'lake-manifest.json').read_text())
assert len(pins['packages'])==10 and pins['name']=='NLAMF22'
assert all(re.fullmatch('[0-9a-f]{40}',p['rev']) for p in pins['packages'])
assert (S/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
assert {p['name']:p['rev'] for p in pins['packages']}['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926'
assert {p['name']:p['rev'] for p in pins['packages']}['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
source={}
for short in ['README.md','solution.md']:
    rel='matrix-functions-and-stability/MF-22/'+short
    data=subprocess.check_output(['git','show','8f04b905eb2e0827b6b84f37d9d080ae1f05b202:'+rel],cwd='/Users/georgestepaniants/Research/OpenProblemsInNLA')
    assert data==(S/'source'/short).read_bytes()
    source[rel]=hashlib.sha256(data).hexdigest()
checks={'phase':'independent complete mathematical source review; mechanical acceptance pending','reviewer':'OpenAI Codex agent /root/next_inequalities','nonimplementing_referee':True,'source_snapshot_file_count':len(inputs),'active_source_file_count':len(proof),'all_current_proof_files_match_held_manifest':True,'full_import_closure_reachable_from_solution':True,'all_ten_frozen_files_unchanged':True,'four_independent_statement_reports_and_four_checks_match_freeze':True,'all22_signatures_match_challenge_modulo_whitespace':True,'signature_checks':sigchecks,'all22_solution_kernel_trust_and_axiom_commands_present':True,'challenge_holes_only':22,'forbidden_active_source_tokens':forbidden,'no_challenge_import':True,'comparator_definition_holes':[],'permitted_axioms_configuration':comp['permitted_axioms'],'source_commit':'8f04b905eb2e0827b6b84f37d9d080ae1f05b202','original_sources_match_git':source,'dependency_revisions':{p['name']:p['rev'] for p in pins['packages']},'external_imports':sorted(external),'all52_retained_input_hashes_valid':True,'local_lean_execution':False,'full_graph_compile_acceptance_claimed':False,'canonical_comparator_acceptance_claimed':False,'status_count_change':False,'historical_metadata_and_default_challenge_target_retained':True}
(R/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'source_files':len(proof),'signature_matches':len(sigchecks),'snapshot_files':len(inputs),'checks_sha256':sha(R/'CHECKS.json')},indent=2))
