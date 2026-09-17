# SP-15 numerical preflight, before proof implementation

No Lean proof or statement freeze exists yet. Test the exact rational point

    (p1,p2,p3,q1,q2,q3,a,b,c,d)=(1,2,3,4,4,4,1,1,1,1).

P=diag(1,2,3), Q=[[4,1,1],[1,4,1+i],[1,1-i,4]].
The leading principal minors of Q should be 4,15,50; P is strictly ordered positive. Define F(u,s)=det(u I+s(P+Q)+PQ). Form the nine real coefficients except the fixed u^3 coefficient, in the monomial order (1,u,s,u²,us,s²,u²s,us²,s³).

The critical proposed finite certificate is rank(DΦ)=9 at this point, witnessed by a nonzero 9-by-9 column minor of the actual 9-by-10 coefficient Jacobian. Its minor index and exact value are to be measured, not assumed. If this fails, preserve the failure and investigate the true coefficient rank before any proof assignment. Such a certificate alone is a prerequisite; it does not prove the universal shifted-singular-value equality or distinct unitary classes.
