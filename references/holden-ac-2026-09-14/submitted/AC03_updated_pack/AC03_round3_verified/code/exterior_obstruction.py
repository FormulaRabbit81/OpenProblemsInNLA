"""Exact exterior-contraction obstruction for cyclic first-normal spaces.

All 24 normalized 17th-root configurations with 16 independent base products
are enumerated. For each, the complete joint exterior-contraction map on
wedge^3(U_A) x wedge^4(U_B) x wedge^3(U_C) has 154350 columns.
Full column rank modulo 101 is a characteristic-zero nonexistence certificate,
not a finite-field enumeration of possible complex normal subspaces.
"""
from __future__ import annotations
from itertools import product,combinations
from collections import defaultdict,Counter
from pathlib import Path
import argparse,json,time
from modular import kernel,rank,check_relation


def configurations():
    result=[]
    for c in range(1,17):
        for others in combinations(range(1,17),3):
            bases=((0,1),(0,)+others,(0,c))
            sums={sum(v)%17 for v in product(*bases)}
            if len(sums)==16:
                missing=next(iter(set(range(17))-sums))
                result.append((bases,missing))
    assert len(result)==24
    return result


def normal_spaces(bases,missing):
    spaces=[]
    for i in range(3):
        products={sum(v)%17 for v in product(*(bases[j] for j in range(3) if j!=i))}
        annihilator=tuple(x for x in range(17) if all((x+y)%17!=missing for y in products))
        assert set(bases[i]).issubset(annihilator)
        spaces.append(tuple(x for x in annihilator if x not in bases[i]))
    assert list(map(len,spaces))==[7,9,7]
    return tuple(spaces)


def coordinate_control(bases,missing,spaces):
    """Find and check a nonzero (3,3,3) exterior kernel control.

The obstruction concerns B dimension FOUR, not THREE. This check prevents
silently replacing the required dimensions by a stronger false assertion.
"""
    for A in combinations(spaces[0],3):
        for C in combinations(spaces[2],3):
            if any((a+b+c)%17==missing for a,b,c in product(A,bases[1],C)):
                continue
            B=[b for b in spaces[1]
               if all((a+b+c)%17!=missing for a,c in product(A,bases[2]))
               and all((a+b+c)%17!=missing for a,c in product(bases[0],C))]
            if len(B)>=3:
                B=tuple(B[:3])
                assert not any((a+b+c)%17==missing for a,b,c in product(A,B,bases[2]))
                assert not any((a+b+c)%17==missing for a,b,c in product(bases[0],B,C))
                return {'A':A,'B':B,'C':C,'dimensions':[3,3,3]}
    # Existence of this particular control is not required by the theorem.
    return None


def verify_instance(bases,missing,prime=101,check_kernel_relations=True):
    spaces=normal_spaces(bases,missing)
    AA=list(combinations(range(7),3))
    BB=list(combinations(range(9),4))
    CC=list(combinations(range(7),3))
    assert len(AA)*len(BB)*len(CC)==154350
    ab_by=defaultdict(list)
    for ai,A in enumerate(AA):
        for bi,B in enumerate(BB):
            charge=(sum(spaces[0][a] for a in A)+sum(spaces[1][b] for b in B))%17
            ab_by[charge].append((ai,bi))
    ab_kernel=[]
    ab_ranks=[]
    ab_domain=[]
    for charge,keys in sorted(ab_by.items()):
        columns=[]
        for ai,bi in keys:
            A,B=AA[ai],BB[bi]
            vector={}
            for m,c in enumerate(bases[2]):
                for a,b in product(range(3),range(4)):
                    if (spaces[0][A[a]]+spaces[1][B[b]]+c)%17==missing:
                        row=(m,A[:a]+A[a+1:],B[:b]+B[b+1:])
                        vector[row]=(-1)**(a+b)
            columns.append(vector)
        current_rank,relations=kernel(columns,prime)
        if check_kernel_relations:
            for relation in relations:
                check_relation(columns,relation,prime)
        ab_ranks.append(current_rank)
        ab_domain.append(len(columns))
        for relation in relations:
            ab_kernel.append((charge,{keys[i]:coefficient for i,coefficient in relation.items()}))
    assert sum(ab_domain)==4410
    assert sum(ab_ranks)+len(ab_kernel)==4410
    by=defaultdict(list)
    for charge,relation in ab_kernel:
        for ci,C in enumerate(CC):
            by[(charge+sum(spaces[2][c] for c in C))%17].append((relation,ci))
    ac,bc={},{}
    for ai,A in enumerate(AA):
        for ci,C in enumerate(CC):
            values=[]
            for m,b in enumerate(bases[1]):
                for a,c in product(range(3),repeat=2):
                    if (spaces[0][A[a]]+spaces[2][C[c]]+b)%17==missing:
                        values.append((m,A[:a]+A[a+1:],C[:c]+C[c+1:],(-1)**(a+c)))
            ac[ai,ci]=values
    for bi,B in enumerate(BB):
        for ci,C in enumerate(CC):
            values=[]
            for m,a in enumerate(bases[0]):
                for b,c in product(range(4),range(3)):
                    if (spaces[1][B[b]]+spaces[2][C[c]]+a)%17==missing:
                        values.append((m,B[:b]+B[b+1:],C[:c]+C[c+1:],(-1)**(b+c)))
            bc[bi,ci]=values
    records=[]
    for charge,keys in sorted(by.items()):
        columns=[]
        for relation,ci in keys:
            vector={}
            for (ai,bi),coefficient in relation.items():
                for m,A,C,sign in ac[ai,ci]:
                    row=(0,m,A,BB[bi],C)
                    vector[row]=(vector.get(row,0)+coefficient*sign)%prime
                for m,B,C,sign in bc[bi,ci]:
                    row=(1,m,AA[ai],B,C)
                    vector[row]=(vector.get(row,0)+coefficient*sign)%prime
            columns.append({key:value for key,value in vector.items() if value})
        columns.sort(key=len)
        current_rank,entries=rank(columns,prime)
        assert current_rank==len(columns), (bases,missing,charge,current_rank,len(columns))
        records.append({'charge':charge,'domain':len(columns),'rank':current_rank,
                        'stored_pivot_entries':entries})
    assert sum(r['domain'] for r in records)==len(ab_kernel)*35
    total_rank=sum(ab_ranks)*35+sum(r['rank'] for r in records)
    assert total_rank==154350
    return {'bases':bases,'missing_character':missing,'normal_spaces':spaces,'prime':prime,
            'full_domain_dimension':154350,'full_rank_mod_prime':total_rank,
            'AB_domain_dimension':4410,'AB_rank':sum(ab_ranks),'AB_kernel_dimension':len(ab_kernel),
            'AB_kernel_relations_independently_checked':check_kernel_relations,
            'remaining_blocks':records,'lower_dimension_coordinate_control':coordinate_control(bases,missing,spaces),
            'conclusion':'No complex normal subspaces of dimensions (3,4,3) satisfy all second-normal conditions.'}


def verify(all_configurations=True,prime=101,progress=False):
    configs=configurations()
    if not all_configurations:
        configs=[(((0,1),(0,2,4,6),(0,8)),16),(((0,1),(0,2,8,10),(0,4)),16)]
    results=[]
    for i,(bases,missing) in enumerate(configs):
        results.append(verify_instance(bases,missing,prime))
        if progress:
            print(f'Exterior certificate {i+1}/{len(configs)}: full rank 154350 modulo {prime}',flush=True)
    return {'status':'PASS','normalization_enumerates_24_configurations':True,
            'tested_configuration_count':len(results),'prime':prime,'instances':results,
            'scope':'Arbitrary holomorphic factor curves at the stated 17-point root configurations, scalar poles at most three; not arbitrary pole orders or arbitrary limiting configurations.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--representatives-only',action='store_true')
    parser.add_argument('--prime',type=int,default=101,choices=(101,103))
    args=parser.parse_args()
    result=verify(not args.representatives_only,args.prime,True)
    root=Path(__file__).resolve().parents[1]
    tag=('representatives_' if args.representatives_only else '')+str(args.prime)
    (root/f'results/exterior_{tag}.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: exact exterior-contraction certificates',flush=True)
