"""Fresh independent finite audits; imports no submitted checker modules."""
from pathlib import Path
from collections import defaultdict, Counter
from fractions import Fraction as F
from itertools import product, permutations, combinations_with_replacement
import argparse, json, time
import sympy as sp

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', required=True, type=Path)
parser.add_argument('--out', required=True, type=Path)
args = parser.parse_args()
SRC = args.repo.resolve() / 'references/holden-ac-2026-09-14/submitted'
args.out.parent.mkdir(parents=True, exist_ok=True)

def cube_floor(n):
    a,b=0,1
    while b**3 <= n: b*=2
    while b-a>1:
        m=(a+b)//2
        if m**3<=n:a=m
        else:b=m
    assert a**3<=n<(a+1)**3
    return a

def cr_interval(n):
    den=10**55;z=cube_floor(n*den**3)
    return F(z,den),F(z+1,den)

def ac01_bound(x):
    d,t,h,v=108,112,330,108;a=x**3+x**4;records=[]
    for step in range(4):
        low=3*cr_interval((t//2)**2)[0]
        records.append({'stage':step,'d':d,'t':t,'v':v,'D':2*d+t,'H':h,
                        'normalized_gap_decimal':str(sp.N(sp.Rational((a+low-h).numerator,(a+low-h).denominator)/h,30))})
        if step==3: return (a+low)/h-1,records
        ell=(t-1)//3
        assert ell>0 and ell%2 and 3*ell+1==t
        a=a*a+2*a*low+3*x*ell*cr_interval(ell)[0]
        d,t,h,v=d*d+2*d*t+3*ell*ell,t*t+2*d*d-6*ell*ell,h*h,v*v+2*v*(t+1)+3*(2*ell+ell*ell)
        assert 2*d+t==328**(2**(step+1))

def small_tensor(rows,degrees,g1,g2):
    def cw(g):
        ans={}
        for i,j in product(range(4),repeat=2):
            if g[i][j]:
                for t in ((0,i+1,j+1),(i+1,0,j+1),(i+1,j+1,0)):
                    ans[t]=g[i][j]
        return ans
    columns=[[(r,rows[r][c]) for r in range(20) if rows[r][c]] for c in range(25)]
    terms=defaultdict(F)
    for left,lc in cw(g1).items():
        for right,rc in cw(g2).items():
            columns3=[columns[5*i+j] for i,j in zip(left,right)]
            for entry in product(*columns3):
                key=tuple(x[0] for x in entry)
                terms[key]+=lc*rc*entry[0][1]*entry[1][1]*entry[2][1]
    count=Counter()
    for key in product(range(20),repeat=3):
        val=terms.get(key,F(0));degree=sum(degrees[k] for k in key)
        if val: count[degree]+=1
        if degree<0: assert val==0, ('negative',key,val)
        expected=0
        if all(k<9 for k in key):
            expected=int(len({k//3 for k in key})==3 and len({k%3 for k in key})==3)
        if key.count(9)==1:
            big=[k for k in key if k!=9]
            if min(big)>=10: expected=int(((big[0]-10)^1)==big[1]-10)
        constant=val if degree==0 else F(0)
        assert constant==expected,('constant',key,constant,expected)
    return dict(sorted(count.items()))

def ac01_seed():
    c=json.loads((SRC/'AC01_round3_research_pack/certificates/small_degeneration.json').read_text())
    rows=[[F(x) for x in row] for row in c['rows']]
    g1=[[F(x) for x in row] for row in c['source_form_1']]
    g2=[[F(x) for x in row] for row in c['source_form_2']]
    degrees=c['row_degrees'];assert sp.Matrix(rows).rank()==20
    hist=small_tensor(rows,degrees,g1,g2)
    rejected=[]
    bad=[r[:] for r in rows];bad[0]=[2*x for x in bad[0]]
    for label,rr,dd in [('scaled main row',bad,degrees),('wrong head degree',rows,[0]*9+[-1]+[1]*10)]:
        try: small_tensor(rr,dd,g1,g2)
        except AssertionError:rejected.append(label)
        else:raise AssertionError('Independent checker accepted '+label)
    B1=sp.Matrix([[-1,0,-1],[0,-1,0],[-1,0,1]])
    B2=sp.Matrix([[1,0,1],[0,-1,0],[1,0,-1]])
    slices=[]
    for c in range(3):
        N=sp.zeros(3)
        for a,b in permutations([x for x in range(3) if x!=c]):N[a,b]=1
        slices.append(N)
    gram=sp.Matrix(3,3,lambda c,d:sp.trace(slices[c].T*B1*slices[d]*B2))
    assert gram==sp.zeros(3) and B1.det()==B2.det()==2
    return {'all_ordered_coefficients':8000,'nonzero_by_degree':hist,'rank':20,
            'core_gram':str(gram),'extra_corruptions_rejected':rejected}

def ac04_group(n,padding=-1):
    # Enumerate group summands directly; target support is independently
    # characterized coordinatewise, without reading a submitted output file.
    G=list(product(range(4),repeat=n)); S={g for g in G if all(g)};w=(1,)*n
    plus=lambda a,b:tuple(x^y for x,y in zip(a,b))
    Fset={s for s in S if plus(s,w) in S};E=set(G)-S-{plus(s,w) for s in S}
    def images(g):
        out=[]
        if g in S:out.append((('main',g),0))
        if g in E:out.append((('large',g),1))
        if g==w:out.append((('head',()),-2))
        return out
    image={g:images(g) for g in G};p=Counter()
    for a,b in product(G,repeat=2):
        for triple in product(image[a],image[b],image[plus(a,b)]):
            p[(tuple(x[0] for x in triple),sum(x[1] for x in triple))]+=1
    for f in Fset:
        for pos in range(3):
            t=[('main',f),('main',plus(f,w))];t.insert(pos,('head',()))
            p[(tuple(t),-2)]+=padding
    p={k:v for k,v in p.items() if v};assert not any(k[1]<0 for k in p)
    actual={k[0]:v for k,v in p.items() if k[1]==0};expected={}
    for a,b in product(S,repeat=2):
        c=plus(a,b)
        if all(c): expected[(('main',a),('main',b),('main',c))]=1
    for a in E:
        for pos in range(3):
            t=[('large',a),('large',plus(a,w))];t.insert(pos,('head',()))
            expected[tuple(t)]=1
    assert actual==expected
    return {'n':n,'source_group_terms':len(G)**2,'s':len(Fset),'t':len(E),
            'constant_terms':len(actual),'nonzero_by_degree':dict(Counter(k[1] for k in p))}

def derivative_blocks():
    S=list(product(range(1,4),repeat=2));zs=[sp.Matrix([-1,1,0]),sp.Matrix([-1,0,1])]
    data=[]
    for charge in product(range(4),repeat=2):
        triples=[t for t in combinations_with_replacement(S,3)
                 if tuple(t[0][j]^t[1][j]^t[2][j] for j in range(2))==charge]
        E=sp.Matrix([[t.count(q) for q in S] for t in triples]);r=E.rank()
        assert r==5 if charge==(0,0) else r==7 if 0 in charge else r==9
        rec={'charge':charge,'rows':len(triples),'rank':r}
        if all(charge):
            Q=sp.Matrix([[sum(a[x[0]-1] for x in t)*sum(b[x[1]-1] for x in t)
                          for a,b in product(zs,repeat=2)] for t in triples])
            # Full augmented rank proves the four mixed columns form a
            # cokernel basis, independent of any chosen left-nullspace basis.
            assert E.row_join(Q).rank()==13
            K=sp.Matrix.vstack(*[v.T for v in E.T.nullspace()]);det=(K*Q).det()
            assert det !=0
            rec.update(augmented_rank=13,mixed_determinant=int(det))
        data.append(rec)
    assert sum(x['rank'] for x in data)==128
    return data

start=time.monotonic()
out={'scope':'Independent finite checks only; general written proofs reviewed separately.'}
out['ac01_seed']=ac01_seed()
gap,states=ac01_bound(F(3876919161,10**9));assert gap>F(1,10**9)
badgap,_=ac01_bound(F(969,250));assert badgap<0
out['ac01_bound']={'states':states,'strict_gap_over_1e9':True,'unsupported_3_876_rejected':True}
rho=F(913,250);c=F(217,100);C=c*c-c
slack=330-rho**3-rho**4-c*cr_interval(328**2)[1]
assert slack>F(1,10) and c**3>F(27,4) and C**3>max(F(27,2),rho**3/3)
out['ac01_tree_anchor']={'slack':str(sp.N(sp.Rational(slack.numerator,slack.denominator),30)),
                         'three_cubed_comparisons_pass':True}
out['ac04_group']=[ac04_group(n) for n in (1,2,3,4,5)]
try:ac04_group(3,padding=1)
except AssertionError:out['ac04_wrong_padding_rejected']=True
else:raise AssertionError('Wrong padding accepted')
out['ac04_derivative_blocks']=derivative_blocks()
lo=F('3.89691367400556951923');hi=F('3.89691367400556951924')
poly=lambda x:(274-x**4)**3-27*3025
assert 274-hi**4>0 and poly(lo)>0>poly(hi)>poly(F('3.896914'))
out['ac04_endpoint_bracket']=[str(lo),str(hi)]
out['elapsed_seconds']=round(time.monotonic()-start,6)
out['all_checks_passed']=True
args.out.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in {'ac04_derivative_blocks','ac01_bound'}},indent=2))
