"""Independent bounded rational-complex checks; not Lean or a universal proof."""
from fractions import Fraction as Q
from dataclasses import dataclass
from pathlib import Path
import hashlib,json
@dataclass(frozen=True)
class C:
    a:Q=Q(0)
    b:Q=Q(0)
    def __add__(s,t):
        t=cc(t);return C(s.a+t.a,s.b+t.b)
    __radd__=__add__
    def __neg__(s):return C(-s.a,-s.b)
    def __sub__(s,t):return s+-cc(t)
    def __rsub__(s,t):return cc(t)+-s
    def __mul__(s,t):
        t=cc(t);return C(s.a*t.a-s.b*t.b,s.a*t.b+s.b*t.a)
    __rmul__=__mul__
    def __truediv__(s,t):
        t=cc(t);d=t.a*t.a+t.b*t.b;assert d!=0
        return C((s.a*t.a+s.b*t.b)/d,(s.b*t.a-s.a*t.b)/d)
    def __pow__(s,n):
        assert n>=0;v=cc(1)
        for _ in range(n):v=v*s
        return v
    def conj(s):return C(s.a,-s.b)
    def nsq(s):return s.a*s.a+s.b*s.b

def cc(t):return t if isinstance(t,C) else C(Q(t))
Z=cc(0);I=C(Q(0),Q(1))
def eye(n):return [[cc(int(i==j)) for j in range(n)] for i in range(n)]
def mm(A,B):return [[sum((a*b for a,b in zip(row,col)),Z) for col in zip(*B)] for row in A]
def plus(A,B):return [[a+b for a,b in zip(ar,br)] for ar,br in zip(A,B)]
def scale(a,A):return [[a*x for x in row] for row in A]
def det(A):
    A=[row[:] for row in A];value=cc(1);n=len(A)
    for j in range(n):
        k=next((k for k in range(j,n) if A[k][j]!=Z),None)
        if k is None:return Z
        if k!=j:A[k],A[j]=A[j],A[k];value=-value
        v=A[j][j];value=value*v
        for k in range(j+1,n):
            q=A[k][j]/v
            for col in range(j+1,n):A[k][col]=A[k][col]-q*A[j][col]
    return value

def padd(a,b):
    out=[0]*max(len(a),len(b))
    for j,v in enumerate(a):out[j]+=v
    for j,v in enumerate(b):out[j]+=v
    while out and out[-1]==0:out.pop()
    return out

def pmul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for j,v in enumerate(a):
        for k,w in enumerate(b):out[j+k]+=v*w
    while out and out[-1]==0:out.pop()
    return out

def ppow(a,n):
    out=[1]
    for _ in range(n):out=pmul(out,a)
    return out

def pscale(v,a):return [v*x for x in a]
aa=[-60,0,6];bb=[0,25];ccp=[-30,0,5];dd=[0,15]
disc=padd(padd(padd(padd(pmul(ppow(bb,2),ppow(ccp,2)),pscale(-4,pmul(aa,ppow(ccp,3)))),pscale(-4,pmul(ppow(bb,3),dd))),pscale(-27,pmul(ppow(aa,2),ppow(dd,2)))),pscale(18,pmul(pmul(aa,bb),pmul(ccp,dd))))
expected=padd(padd(pscale(-25,pmul([0,0,0,0,1],[34200,0,-3337,0,120])),[0,0,-5269500]),[-6480000])
assert disc==expected
assert [3337**2+5280431,-2*240*3337,240**2]==[480*34200,-480*3337,480*120]
BB={-1:[[-1,0],[-5,0]],0:[[0,-5],[16,-5]],1:[[-5,16],[-5,0]],2:[[0,-5],[0,-1]]}
CC={-1:[[1,0],[7,0]],0:[[24,7],[0,25]],1:[[-25,0],[-7,-24]],2:[[0,-7],[0,-1]]}
zero2=[[0,0],[0,0]]
counts={'symbolic_discriminant_coefficient_identity':1,'symbolic_completed_square_coefficient_identity':1,'transfer_polynomial_points':0,'cayley_points':0,'coprimality_elimination_data':0,'actual_Green_inverse_dimensions':0,'every_state_entry_identities':0}
for rho in [Q(1,2),Q(1),Q(2),Q(3),Q(4)]:
    r=cc(rho);A=-r-6*I;B=-7*r-30*I;C0=7*r-30*I;D=-25*r-30*I;E=r-6*I;F=25*r-30*I
    a=30-r**2-10*I*r;b=24*r**2+80*I*r-240;c=420-46*r**2
    L=[[A,B],[B,D]];ld=det(L);assert ld==24*a and ld!=Z
    Linv=scale(cc(1)/ld,[[D,-B],[-B,A]])
    assert mm(L,Linv)==mm(Linv,L)==eye(2)
    top=mm(Linv,[[24*r,-96*I,-F,-C0],[-96*I,-24*r,-C0,-E]])
    T=top+[[cc(1),Z,Z,Z],[Z,cc(1),Z,Z]];G=Linv+[[Z,Z],[Z,Z]]
    num=lambda z:a+(-120-r**2+22*I*r)*z+2*(r**2+18)*z**2
    den=lambda z:a+b*z+c*z**2+b.conj()*z**3+a.conj()*z**4
    quart=lambda z:a*z**4+b*z**3+c*z**2+b.conj()*z+a.conj()
    quo=lambda z:a*z**3+(a+b)*z**2-(a.conj()+b.conj())*z-a.conj()
    realcub=lambda z:6*(r**2-10)*z**3+25*r*z**2+5*(r**2-6)*z+15*r
    assert quo(cc(1))==120*I*r and quo(cc(-1))==48*(r**2-10)
    assert realcub(-I)==-I*a
    assert 3*a-2*(a+b)-(a.conj()+b.conj())+100*I*r==-72*(r**2-10)
    for z in [cc(0),cc(1),cc(-1),I,-I,I/3,cc(2)+I]:
        M=plus(eye(4),scale(-z,T))
        assert det(M)==den(z)/a
        assert det([row[1:] for row in M[1:]])==num(z)/a
        assert det(plus(scale(z,eye(4)),scale(cc(-1),T)))==quart(z)/a
        assert quart(z)==(z-1)*quo(z)
        counts['transfer_polynomial_points']+=1
        if cc(1)-I*z!=Z:
            assert (cc(1)-I*z)**3*quo((cc(1)+I*z)/(cc(1)-I*z))==8*I*realcub(z)
            counts['cayley_points']+=1
    resultant=(C0*D-B*E)**2-(C0*(24*r)-(96*I)*E)*((96*I)*D-B*(24*r))
    assert resultant==2177280+946944*r**2+I*(622080*r+241920*r**3)
    zden=7*r**2+30+22*I*r;z0=(7*r**2-24+34*I*r)/zden;y=rho*rho
    RR=134136+32436*y-10404*y*y;JJ=-103032-40632*y+840*y*y
    assert zden**2*num(z0)==RR+I*r*JJ
    assert 70*RR+867*JJ==-79939224-32957424*y
    counts['coprimality_elimination_data']+=1
    powers=[eye(4)]
    for _ in range(5):powers.append(mm(powers[-1],T))
    outer=[[cc(int(i==0 and j==0)) for j in range(4)] for i in range(4)]
    for n in range(1,6):
        an=powers[n][0][0];assert an!=Z
        kernels={}
        for j in range(n+1):
            for ell in range(n):
                first=mm(powers[j-1-ell],G) if ell<j else [[Z,Z] for _ in range(4)]
                correction=mm(mm(mm(powers[j],outer),powers[n-1-ell]),G)
                kernels[j,ell]=plus(first,scale(-cc(1)/an,correction))
        Qinverse=[[kernels[i//2+(i%2),k//2][i%2][k%2] for k in range(2*n)] for i in range(2*n)]
        M=[]
        for row in range(2*n):
            vals=[]
            for col in range(2*n):
                offset=row//2-col//2
                v=6*I*BB.get(offset,zero2)[row%2][col%2]-r*CC.get(offset,zero2)[row%2][col%2]
                assert (v/80).nsq()<=(2+rho)**2
                vals.append(v)
            M.append(vals)
        assert mm(M,Qinverse)==eye(2*n) and mm(Qinverse,M)==eye(2*n)
        for j in range(n+1):
            for col in range(2*n):
                def coordinate(k,c0):return Qinverse[2*k+c0][col] if 0<=k<n else Z
                actual=[coordinate(j,0),coordinate(j-1,1),coordinate(j-1,0),coordinate(j-2,1)]
                expected=[kernels[j,col//2][i][col%2] for i in range(4)]
                assert actual==expected
                counts['every_state_entry_identities']+=4
        counts['actual_Green_inverse_dimensions']+=1
p=Path(__file__)
(p.parent/'EXACT-DIAGNOSTICS.json').write_text(json.dumps({'scope':'Independent bounded exact rational-complex diagnostics and two exact polynomial coefficient identities; not universal Lean proofs, root isolation or norm verification.',
 'script_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'counts':counts,'all_passed':True},indent=2)+'\n')
print(json.dumps(counts,indent=2))
