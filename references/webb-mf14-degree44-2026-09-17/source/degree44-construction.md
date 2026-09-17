## The construction now reaches degree \(44\)

I strengthened the earlier degree-\(43\) result to
\[
\boxed{\mathbb C[x]_{\le44}\subseteq\overline{\mathcal P_7}^{\,Z},}
\]
with an exact \(45\times45\) Jacobian certificate
\[
\boxed{\det J=256.}
\]

This refutes **the equality \(d_7=42\) asked in MF-14**, in its original complex-coefficient model and full ambient coefficient space. The canonical entry currently records degree-\(42\) coverage as a verified partial result, while leaving the maximal-degree equality open. citeturn381533view0

The contribution package contains a seven-page proof, compilable LaTeX, a dependency-free exact verifier, the complete integer Jacobian, execution logs, an internal audit, and a draft resolution issue. The checks also passed after extracting the finished archive.

**[Complete contribution package](sandbox:/mnt/data/mf14_degree44_contribution.zip)**

[Proof PDF](sandbox:/mnt/data/mf14_degree44/references/mf14-degree44-2026-09-17/proof.pdf) · [LaTeX source](sandbox:/mnt/data/mf14_degree44/references/mf14-degree44-2026-09-17/proof.tex) · [Exact verifier](sandbox:/mnt/data/mf14_degree44/references/mf14-degree44-2026-09-17/verify_degree44.py) · [Draft GitHub issue](sandbox:/mnt/data/mf14_degree44/ISSUE_DRAFT.md)

The proof has passed my internal mathematical and computational checks, **not independent referee review**. The appropriate initial submission status is therefore **Solution claimed**, following the repository’s distinction between a complete resolution claim and an independently audited solution. No issue or pull request has been posted. citeturn381533view2

## 1. What the new result adds

Write
\[
X_7=\overline{\mathcal P_7}^{\,Z}\subseteq\mathbb C[x]_{\le128},
\qquad
d_7=\max\{d:\mathbb C[x]_{\le d}\subseteq X_7\}.
\]

The manuscript establishes \(d_7\ge44\). Combined with Jarlebring and Lorentzon’s dimension theorem, a separate argument gives
\[
\boxed{44\le d_7\le47.}
\]
The upper-bound argument appears below; determining which of these four integers is the exact maximum remains a separate question. The original source’s Conjecture 13 asks specifically whether that maximum is \(42\), so the lower bound \(44\) already settles that conjectured equality negatively. citeturn301643view4

The new ingredient is a stronger **simultaneous four-product border construction**. It supplies a general degree-\(12\) polynomial while retaining two lower-degree intermediates needed by the remaining products. Merely knowing that degree-\(12\) polynomials individually belong to the four-product closure would not justify this continuation.

Colbrook’s existing degree-\(42\) result remains valid and retains its credit. Its exact coefficient-map certificate concerns a fixed seven-product scheme; the construction here exploits degenerating intermediate computations instead. citeturn301643view2

## 2. The essential lemma: degree twelve with the intermediates preserved

Let \(\mathcal A_4\) be the set of ordered quadruples of polynomials **simultaneously available** after at most four products, starting from \(1,x\), and let
\[
\mathcal B_4=\overline{\mathcal A_4}^{\,Z}
\subseteq\bigl(\mathbb C[x]_{\le16}\bigr)^4.
\]

The central lemma is:

> **Simultaneous border-availability lemma.** For every \(\alpha,\beta\in\mathbb C\) and every \(P\in\mathbb C[x]_{\le12}\),
> \[
> \boxed{\left(x^2,\ x^4+\alpha x^3,\ x^5+\beta x^3,\ P\right)\in\mathcal B_4.}
> \]

This is the part that required the most careful checking.

### Three products prepare a degenerating intermediate

Set
\[
Q=x^4+\alpha x^3,\qquad
\eta=\beta+\alpha^2,
\]
and introduce a scalar \(\gamma\in\mathbb C\). For small nonzero \(t\), define
\[
a=t^6,\qquad b=\gamma t^3,\qquad
R_t=aQ^2+b x^2Q+xQ+\eta x^3.
\]

The first two products compute \(x^2\) and \(Q=x^2(x^2+\alpha x)\). Despite its expanded appearance, \(R_t\) requires only **one further product**. Indeed, with
\[
g=b-a,\qquad
\sigma=\frac{\eta-1+\alpha g}{b-2a},\qquad
\rho=1-a\sigma,
\]
there is the exact identity
\[
\boxed{
R_t=(aQ+\rho x+g x^2)(Q+\sigma x+x^2)
-gQ-\rho\sigma x^2.
}
\]
The denominator is nonzero for sufficiently small nonzero \(t\), including when \(\gamma=0\).

Moreover,
\[
R_t-\alpha Q\longrightarrow x^5+\beta x^3.
\]

### The fourth product is dense in a twelve-dimensional product span

Define
\[
V_t=\operatorname{span}\{1,x,x^2,Q,R_t\},
\qquad
W_t=\operatorname{span}\{uv:u,v\in V_t\}.
\]
An elementary product-span calculation gives
\[
W_t=
\mathbb C[x]_{\le6}
+\operatorname{span}\{Q^2,xR_t,x^2R_t,QR_t,R_t^2\},
\qquad
\dim W_t=12.
\]

Consider
\[
\Psi_t:V_t^3\longrightarrow W_t,\qquad
(u,v,w)\longmapsto uv+w.
\]
Its outputs cost one additional product. At
\[
u=R_t,\qquad v=Q+\lambda x^2,\qquad \lambda=\eta+1,
\]
the differential spans all of \(W_t\).

The decisive coefficient in this spanning calculation is
\[
\kappa_t=-1+\alpha\lambda(b-a\lambda)\longrightarrow-1.
\]
Thus the argument does not omit an exceptional choice of \(\alpha,\beta,\gamma\). The complete spanning identity is given in the manuscript and checked symbolically by the verifier.

Full differential rank implies that \(\Psi_t(V_t^3)\) is Zariski dense in \(W_t\). Consequently,
\[
\left(x^2,Q,R_t-\alpha Q,p\right)\in\mathcal B_4
\qquad\text{for every }p\in W_t.
\]

**This is a closure statement, not a claim that an arbitrary sum of products costs one product.**

### A tunable limiting direction supplies degree twelve

The improvement over the previous construction comes from the scaling
\[
q_t(y)=y^4+\alpha t^2y^3,
\]
\[
r_t(y)=q_t(y)^2+\gamma t\,y^2q_t(y)+yq_t(y)+\eta t^4y^3.
\]
These satisfy
\[
q_t(t^2x)=t^8Q(x),\qquad
r_t(t^2x)=t^{10}R_t(x).
\]

Choose analytic coefficients \(u_1(t),\ldots,u_4(t)\) so that
\[
E_t(y)=yr_t-u_1y^2r_t-u_2q_t^2-u_3q_tr_t-u_4r_t^2
\]
has zero coefficients in degrees \(7,8,9,10\).

The relevant \(4\times4\) coefficient matrix at \(t=0\) is
\[
M(0)=
\begin{pmatrix}
1&0&0&0\\
0&1&0&0\\
0&0&1&0\\
1&0&0&1
\end{pmatrix},
\qquad \det M(0)=1,
\]
so the analytic elimination is legitimate. Solving through second order gives
\[
u(t)=
\begin{pmatrix}
\gamma t\\
-\gamma^2t^2\\
1\\
-2\gamma t
\end{pmatrix}
+O(t^3),
\]
and hence
\[
[y^{11}]E_t=(4\gamma^2-3\alpha)t^2+O(t^3),
\qquad
[y^{12}]E_t=-1+O(t^3).
\]

After removing the degree-at-most-six part and rescaling, this produces a polynomial \(Z_t\in W_t\) satisfying
\[
\boxed{Z_t\longrightarrow x^{12}+(3\alpha-4\gamma^2)x^{11}.}
\]

All coefficients above degree twelve tend to zero. The low-degree subtraction is justified inside the **product span** \(W_t\); it is not an assumed free truncation of a circuit output.

Meanwhile,
\[
1,x,\ldots,x^6,\quad x^2R_t,\quad Q^2,\quad QR_t,\quad R_t^2
\]
converge to a triangular basis of \(\mathbb C[x]_{\le10}\).

For a target polynomial with coefficients \(p_{12}\ne0\) and \(p_{11}\), choose
\[
\gamma^2=\frac{3\alpha-p_{11}/p_{12}}4.
\]
This matches both leading coefficients, and the triangular basis supplies the remainder. The case \(p_{12}=0\) follows by closedness, applying the result to \(P+\varepsilon x^{12}\) and taking \(\varepsilon\to0\).

That proves the joint-availability lemma.

## 3. Three further products reach degree \(44\)

Take
\[
Q=x^4+\alpha x^3,\qquad
R=x^5+\beta x^3,\qquad
P=x^{12}+\sum_{j\in J}\xi_jx^j,
\]
where
\[
J=\{3,6,7,8,9,10,11\}.
\]

Define the ordered lists
\[
L_3=(x,x^2,Q),\qquad
L_4=(x,x^2,Q,R),\qquad
L_5=(x,x^2,Q,R,P).
\]
Use the remaining three products as follows:
\[
\begin{aligned}
F&=(P+\mathbf u\cdot L_4)(R+\mathbf v\cdot L_3),\\
G&=(F+\mathbf a\cdot L_5)(R+\mathbf b\cdot L_3),\\
H&=(G+\mathbf c\cdot L_6)(G+\mathbf d\cdot L_6),
\end{aligned}
\qquad
L_6=(x,x^2,Q,R,P,F).
\]
Finally, form the free linear combination
\[
p=\mathbf z\cdot(1,x,x^2,Q,R,P,F,G,H).
\]

The three product degrees are
\[
17,\qquad22,\qquad44.
\]
There are precisely
\[
\underbrace{2+7}_{\alpha,\beta,\boldsymbol\xi}
+\underbrace{4+3}_{\mathbf u,\mathbf v}
+\underbrace{5+3}_{\mathbf a,\mathbf b}
+\underbrace{6+6}_{\mathbf c,\mathbf d}
+\underbrace{9}_{\mathbf z}
=45
\]
parameters. Thus this defines a polynomial coefficient map
\[
\Phi:\mathbb C^{45}\longrightarrow\mathbb C[x]_{\le44}.
\]

Every value of \(\Phi\) belongs to \(X_7\). To justify that statement, fix the continuation parameters and regard the last three products as a polynomial map \(T\) on the jointly available quadruple. Zariski continuity gives
\[
T(\mathcal B_4)
\subseteq\overline{T(\mathcal A_4)}^{\,Z}
\subseteq X_7.
\]

The statement is in the **full degree-\(128\) ambient space**. It does not discard unwanted high-degree coefficients of approximating computations.

## 4. The certificate is exact and reproducible

Order the parameters as
\[
(\alpha,\beta,\xi_3,\xi_6,\xi_7,\xi_8,\xi_9,\xi_{10},\xi_{11},
\mathbf u,\mathbf v,\mathbf a,\mathbf b,\mathbf c,\mathbf d,\mathbf z),
\]
with vector entries in their listed order and \(\mathbf z=(z_0,\ldots,z_8)\).

Set all parameters to zero except
\[
\boxed{\alpha=b_2=d_3=d_5=d_6=z_8=1.}
\]

At this point,
\[
Q=x^4+x^3,\qquad R=x^5,\qquad P=x^{12},
\]
\[
F=x^{17},\qquad
G=x^{22}+x^{19},\qquad
H=G(G+Q+P+F).
\]

The integer Jacobian, with coefficient rows ordered by degrees \(0,\ldots,44\), satisfies
\[
\boxed{\det D\Phi=256.}
\]
Every entry is between \(0\) and \(6\).

The verifier constructs that matrix in two separately coded ways: from the manuscript’s analytical derivative table using dense polynomial arithmetic, and by directional automatic differentiation of the complete circuit using sparse polynomial arithmetic. They agree entrywise. **Neither computation truncates a circuit or Jacobian polynomial.**

For example, at the certificate point put
\[
B=R+x^2,\qquad
K=2G+Q+P+F,\qquad
L=KB+G.
\]
The first derivative columns are
\[
\frac{\partial p}{\partial\alpha}=Gx^3,
\qquad
\frac{\partial p}{\partial\beta}=(LP+KF)x^3,
\]
and
\[
\frac{\partial p}{\partial\xi_j}=(LR+G)x^j,\qquad j\in J.
\]
The manuscript lists all 45 columns.

Exact fraction-free elimination gives \(256\), checking every division for exactness. A separate modular elimination implementation gives
\[
\det J\equiv1\pmod3,\qquad
\det J\equiv54\pmod{101},\qquad
\det J\equiv256\pmod{1009}.
\]

Run the supplied file with:
```bash
python3 verify_degree44.py
python3 -O verify_degree44.py
```
Both executions passed, including from the extracted contribution archive. The recorded output includes:
```text
45 x 45 Jacobians: analytical table and untruncated directional AD agree entrywise
Exact integer determinant: 256
Independent modular determinants: {'3': 1, '101': 54, '1009': 256}
All exact checks passed. No circuit/Jacobian polynomial was truncated.
```

Since the differential is nonsingular, \(\Phi\) has Zariski-dense image in \(\mathbb C[x]_{\le44}\). Its image lies in the closed set \(X_7\). Therefore
\[
\boxed{\mathbb C[x]_{\le44}\subseteq X_7.}
\]

## 5. Why the upper bound is \(47\), not merely \(48\)

Jarlebring and Lorentzon’s Theorem 10 gives
\[
\dim X_7=7^2=49.
\]
This is the only external mathematical input to the additional upper bound; the degree-\(44\) theorem does not depend on it. citeturn301643view3

The universal seven-product circuit map has an affine parameter space, so its image closure \(X_7\) is irreducible. Suppose
\[
\mathbb C[x]_{\le48}\subseteq X_7.
\]
The left side is a closed subvariety of dimension \(49\), equal to the dimension of \(X_7\). Irreducibility would force
\[
X_7=\mathbb C[x]_{\le48}.
\]
But seven successive squarings compute \(x^{128}\), so \(x^{128}\in X_7\), a contradiction.

Hence
\[
\boxed{44\le d_7\le47.}
\]

## What to submit

The proposed contribution is a **negative-resolution claim for MF-14**, supported by Theorem 1 and Lemma 2 of the manuscript, the exact determinant certificate in equation (25), and the accompanying verifier. The draft issue identifies those locators, preserves the original target and earlier credit, and follows the repository’s correction-or-resolution procedure. citeturn381533view1

The supplied *Stellar Colosseum* paper informed the staged construction, falsification, and final target audit. Its many-agent harness was not executed here, and separately coded checks should not be described as independent referees. citeturn301643view0

The outstanding review question is whether a fresh reviewer accepts the **joint four-product border lemma and its continuation**, not whether a floating-point rank calculation is convincing. The finite certificate has been checked exactly. The manuscript makes no claim about the exact new maximum, exact representation of every degree-\(44\) polynomial, real Euclidean density, or numerical stability.