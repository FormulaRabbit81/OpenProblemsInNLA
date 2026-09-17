"""Independent IV-03 statement hash checks and finite vertex diagnostics."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,subprocess
p=Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
receipt=json.loads((p/'statement-typecheck.json').read_text())
assert receipt['exit_code']==0
for name,h in receipt['sha256'].items():assert sha((p/name).read_bytes())==h,name
source=json.loads((p/'SOURCE_PROVENANCE.json').read_text())
sources={}
for item in source['sources']:
    content=subprocess.check_output(['git','show',source['source_commit']+':'+item['path']],cwd='/Users/sholden/Projects/OpenProblemsInNLA')
    assert sha(content)==item['sha256'];sources[item['path']]=sha(content)
log=(p/'statement-referee-1-typecheck.log').read_text()
assert log.count('declaration uses `sorry`')==4 and 'error:' not in log
samples=0
for n in range(1,5):
    lower=[[Q(i-2*j-1) for j in range(n)] for i in range(n)]
    upper=[[lower[i][j]+Q((i+j)%3) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            for s in [-1,1]:
                for k in range(n):
                    for l in range(n):
                        sign=(1 if k!=i else -1)*(1 if l!=j else -1)*s
                        c=(lower[k][l]+upper[k][l])/2;r=(upper[k][l]-lower[k][l])/2
                        v=c+sign*r
                        assert lower[k][l]<=v<=upper[k][l]
                        assert v==(upper[k][l] if sign==1 else lower[k][l])
                        if s==-1 and k==i and l==j:assert v==lower[i][j]
                samples+=1
assert samples==60
files=list(receipt['sha256'])+['lean-toolchain','LICENSE','statement-typecheck.json','statement-referee-1-typecheck.log','reviews/referee-1-check.py']
out={'verdict':'APPROVE','phase':'statement only','reviewer':'Independent Codex AI agent /root/iv06_statement_referee_2, referee 1','files_sha256':{f:sha((p/f).read_bytes()) for f in files},'sources_sha256':sources,'source_commit':source['source_commit'],'independent_typecheck':{'command':['lake','env','lean','Challenge.lean'],'runtime':'/private/tmp/nla-lean-runtime/lean-4.33.1-darwin_aarch64/bin','exit_code':0,'intentional_placeholders':4},'finite_diagnostics':{'vertex_samples':60,'dimensions':[1,2,3,4],'included':'both signs, zero widths, negative endpoints, diagonal and off-diagonal ordered vertex pairs','limitation':'Finite exact endpoint arithmetic only, not proof of all-dimensional criterion'},'limitations':['No proof bodies reviewed','No final LeanCert export audit or Linux Comparator run','Publication metadata and final completion evidence remain subsequent work']}
(p/'reviews/referee-1-statement-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'verdict':'APPROVE','vertices_checked':samples,'source_files':len(sources),'hashed_files':len(files)}))
