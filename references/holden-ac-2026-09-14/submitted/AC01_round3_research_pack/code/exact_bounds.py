"""Integer-cube and rational certificates for the new bound and tree limitation."""
from __future__ import annotations
from fractions import Fraction as F
import random


def icbrt(n:int)->int:
    if type(n) is not int or n<0:raise ValueError('A nonnegative integer is required')
    lo=0;hi=1 << ((n.bit_length()+2)//3)
    while lo+1<hi:
        m=(lo+hi)//2
        if m*m*m<=n:lo=m
        else:hi=m
    return hi if hi**3<=n else lo


def radical(n,den=10**40):
    return {'radicand':n,'denominator':den,'floor_numerator':icbrt(n*den**3)}


def enclosure(obj):
    n,d,z=(obj[k] for k in ('radicand','denominator','floor_numerator'))
    if any(type(x) is not int for x in (n,d,z)) or n<0 or d<=0 or z<0:
        raise AssertionError('Bad radical certificate fields')
    if not z**3<=n*d**3<(z+1)**3:raise AssertionError('Integer cube enclosure failed')
    return F(z,d),F(z+1,d)


def decimal_floor(x,digits=24):
    x=F(x);z=x.numerator*10**digits//x.denominator
    if z<0:return '-'+decimal_ceil(-x,digits)
    return f'{z//10**digits}.{z%10**digits:0{digits}d}'


def decimal_ceil(x,digits=24):
    x=F(x);z=-((-x.numerator*10**digits)//x.denominator)
    return f'{z//10**digits}.{z%10**digits:0{digits}d}'


def sequence(steps=3):
    d,t,h,v=108,112,330,108;states=[]
    for j in range(steps+1):
        rec={'stage':j,'active_main_dimension':d,'actual_main_dimension':v,
             'cw_size':t,'source_form_rank':2*d+t,'spectral_source_upper':h}
        if j<steps:
            if d%3 or t%6!=4:raise AssertionError('P-lift congruence invariant failed')
            ell=(t-1)//3
            if ell%2!=1 or 3*ell+1!=t:raise AssertionError('Incorrect odd lift size')
            m=3*ell**2;rec.update(lift_size=ell,retained_active_dimension=m,
                                    retained_actual_dimension=3*(2*ell+ell**2))
        states.append(rec)
        if j<steps:
            d,t,h,v=d*d+2*d*t+m,t*t+2*d*d-2*m,h*h,v*v+2*v*(t+1)+3*(2*ell+ell**2)
    return states


def make_bound_certificate():
    states=sequence();rs={}
    for st in states:
        j=st['stage'];rs[f'cw_{j}']=radical((st['cw_size']//2)**2)
        if j<3:rs[f'lift_{j}']=radical(st['lift_size'])
    return {'schema':'p-lift-bound-v1','upper_bound':'3876919161/1000000000',
            'stages':states,'radicals':rs,'required_relative_margin':'1/1000000000'}


def verify_bound(data):
    if data.get('schema')!='p-lift-bound-v1':raise AssertionError('Wrong bound schema')
    states=sequence()
    if states!=data['stages']:raise AssertionError('Incorrect integer recurrence')
    x=F(data['upper_bound']);margin=F(data['required_relative_margin'])
    if not 3<x<4 or margin!=F(1,10**9):raise AssertionError('Incorrect bound parameters')
    a=x**3+x**4;slacks=[]
    for st in states:
        j=st['stage'];obj=data['radicals'][f'cw_{j}']
        if obj['radicand']!=(st['cw_size']//2)**2:raise AssertionError('Wrong CW radicand')
        q=3*enclosure(obj)[0];h=st['spectral_source_upper']
        slacks.append({'stage':j,'relative_gap_lower_decimal_floor':decimal_floor((a+q)/h-1)})
        if j<3:
            ell=st['lift_size'];r=data['radicals'][f'lift_{j}']
            if r['radicand']!=ell:raise AssertionError('Wrong lift radicand')
            z=3*x*ell*enclosure(r)[0]
            a=a*a+2*a*q+z
    if a+q<=h*(1+margin):raise AssertionError('The claimed upper bound is not certified')
    return {'upper_bound':str(x),'stages':states,'radical_enclosures_checked':len(data['radicals']),
            'relative_gaps':slacks,'final_relative_gap_lower_decimal_floor':decimal_floor((a+q)/h-1),
            'exact_final_gap':str((a+q)/h-1),'arithmetic':'integer cubing and exact fractions'}


def make_barrier_certificate():
    return {'schema':'all-binary-tree-envelope-v1','candidate_rho':'913/250',
            'c':'217/100','C':'25389/10000','D':328,'H':330,
            'D_two_thirds':radical(328**2),'required_leaf_slack':'1/10'}


def verify_barrier(data):
    if data.get('schema')!='all-binary-tree-envelope-v1':raise AssertionError('Wrong barrier schema')
    rho,c,C=(F(data[k]) for k in ['candidate_rho','c','C'])
    if not 3<rho<=4 or c!=F(217,100) or C!=F(25389,10000):raise AssertionError('Wrong envelope constants')
    if data['D']!=328 or data['H']!=330:raise AssertionError('Wrong seed state')
    if C!=c*c-c:raise AssertionError('The envelope identity failed')
    # kappa^3=27/4; coordinate-graph coefficient^3=27/2;
    # P-lift coefficient at this fixed candidate rho has cube rho**3/3.
    if not F(27,4)<c**3 or not F(27,2)<C**3 or not rho**3/F(3)<C**3:
        raise AssertionError('An envelope coefficient comparison failed')
    if data['D_two_thirds']['radicand']!=328**2:raise AssertionError('Wrong leaf radicand')
    dhi=enclosure(data['D_two_thirds'])[1]
    slack=330-rho**3-rho**4-c*dhi
    if F(data['required_leaf_slack'])!=F(1,10) or slack<=F(1,10):
        raise AssertionError('The leaf anchor does not certify this barrier candidate')
    return {'candidate_rho':str(rho),'leaf_slack_lower_decimal_floor':decimal_floor(slack),
            'c':str(c),'C':str(C),'exact_leaf_slack_lower':str(slack),
            'scope':'Scalar recurrence inequalities from the fixed seed; every finite binary tree. '
                    'Not a tensor-rank lower bound or a spectral point.'}


def verify_finite_mixed_trees():
    """Supplementary finite tests, not a substitute for the all-tree proof."""
    rho=F(913,250);rng=random.Random(271828);records=[]
    def leaf():return (108,112,330,rho**3+rho**4,1)
    def combine(left,right):
        d1,t1,h1,a1,n1=left;d2,t2,h2,a2,n2=right
        if t1%6!=4 or t2%6!=4:raise AssertionError('Odd lift invariant failed')
        l1,l2=(t1-1)//3,(t2-1)//3;m=3*l1*l2
        q1=3*enclosure(radical((t1//2)**2))[1]
        q2=3*enclosure(radical((t2//2)**2))[1]
        z=3*rho*enclosure(radical((l1*l2)**2))[1]
        a=a1*a2+a1*q2+a2*q1+z
        d=d1*d2+d1*t2+t1*d2+m;t=t1*t2+2*d1*d2-2*m;h=h1*h2
        if 2*d+t!=(2*d1+t1)*(2*d2+t2):raise AssertionError('Mixed dimension identity failed')
        q=3*enclosure(radical((t//2)**2))[1]
        if a+q>=h:raise AssertionError('Finite barrier test failed')
        return (d,t,h,a,n1+n2)
    for n in range(2,17):
        for style in ['left_comb','random']:
            nodes=[leaf() for _ in range(n)]
            while len(nodes)>1:
                if style=='left_comb':a,b=nodes.pop(0),nodes.pop(0)
                else:
                    a=nodes.pop(rng.randrange(len(nodes)));b=nodes.pop(rng.randrange(len(nodes)))
                nodes.insert(0,combine(a,b))
            d,t,h,a,_=nodes[0]
            records.append({'leaves':n,'shape':style,'root_CW_size':t,'strict_test_passed':True})
    return records
