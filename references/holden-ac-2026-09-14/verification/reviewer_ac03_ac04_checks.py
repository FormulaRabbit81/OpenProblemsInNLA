from itertools import product, combinations_with_replacement
from collections import defaultdict
from fractions import Fraction as F
import json

def rank(mat):
    a=[[F(x) for x in row] for row in mat]; i=0
    for j in range(len(a[0])):
        k=next((k for k in range(i,len(a)) if a[k][j]),None)
        if k is None: continue
        a[i],a[k]=a[k],a[i]; z=a[i][j]; a[i]=[x/z for x in a[i]]
        for k in range(i+1,len(a)):
            if a[k][j]:
                z=a[k][j]; a[k]=[x-z*y for x,y in zip(a[k],a[i])]
        i+=1
        if i==len(a): break
    return i
out={}
for n in range(1,5):
    r=4**n; S={sum(x*4**j for j,x in enumerate(xs)) for xs in product((1,2,3),repeat=n)}
    w=sum(4**j for j in range(n)); FF=S & {x^w for x in S}; E=set(range(r))-(S|{x^w for x in S})
    coeff=defaultdict(int)
    def terms(g):
        return ([((0,g),0)] if g in S else []) + ([((1,g),1)] if g in E else []) + ([((2,0),-2)] if g==w else [])
    for x,y in product(range(r), repeat=2):
        for terms3 in product(terms(x),terms(y),terms(x^y)):
            coeff[(tuple(t[0] for t in terms3),sum(t[1] for t in terms3))]+=1
    for f in FF:
        for k in range(3):
            coords=[(0,f),(0,f^w)];coords.insert(k,(2,0));coeff[(tuple(coords),-2)]-=1
    assert not any(c for (coord,p),c in coeff.items() if p<0)
    actual={coord:c for (coord,p),c in coeff.items() if p==0 and c}
    expect={tuple((0,g) for g in (x,y,x^y)):1 for x,y in product(S,repeat=2) if x^y in S}
    for e in E:
        for k in range(3):
            coords=[(1,e),(1,e^w)];coords.insert(k,(2,0));expect[tuple(coords)]=1
    assert actual==expect
    out[f'extraction_n{n}']={'terms':len(actual),'r':r,'s':len(FF),'t':len(E)}
S=list(product((1,2,3),repeat=2));blocks=[]
for I,J in product(range(4),repeat=2):
    triples=[tr for tr in combinations_with_replacement(S,3) if tr[0][0]^tr[1][0]^tr[2][0]==I and tr[0][1]^tr[1][1]^tr[2][1]==J]
    a=[[tr.count(q) for q in S] for tr in triples]; rr=rank(a)
    assert rr==(5 if (I,J)==(0,0) else 7 if I==0 or J==0 else 9)
    if I and J:
        basis=[(-1,1,0),(-1,0,1)]
        q=[[sum(u[x-1] for x,y in tr)*sum(v[y-1] for x,y in tr) for u,v in product(basis,repeat=2)] for tr in triples]
        assert rank([x+y for x,y in zip(a,q)])==13
    blocks.append((I,J,len(a),rr))
out['all_derivative_and_mixed_blocks']=blocks
for x,sign in [(F('3.89691367400556951923'),1),(F('3.89691367400556951924'),-1),(F('3.896914'),-1)]:
    z=274-x**4; assert z>0 and sign*(z**3-81675)>0
out['rational_endpoint']='PASS'
M={(3*i+j,3*j+k,3*k+i) for i,j,k in product(range(3),repeat=3)}
core=set(product((3,6),(3,4,6,7),(6,7)))
assert M.isdisjoint(core) and len(core)==16
mapping={x:'l' for x in M}|{x:str(x) for x in core}
def minor(a,b):
    cross1=(a[0],b[1],b[2]);cross2=(b[0],a[1],a[2])
    assert cross1 not in mapping or cross2 not in mapping
    return mapping[a],mapping[b]
assert minor((0,0,0),(4,3,1))==('l','l')
for b in core: assert minor((0,0,0),b)==('l',str(b))
out['ac03_restricted_ideal_17_extra_monomials']='PASS'
print(json.dumps(out,indent=2))
