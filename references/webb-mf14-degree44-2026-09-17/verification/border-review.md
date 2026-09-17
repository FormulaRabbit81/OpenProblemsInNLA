# Independent review: simultaneous four-product border lemma

Verdict: **PASS. No substantive mathematical gap found.**

This review concerns the simultaneous border lemma and its continuation into a
seven-product circuit. It does not certify the separate 45-by-45 Jacobian or
reprove the external dimension theorem. It is an independent AI-agent review,
not external human referee approval or proof-assistant verification.

## Scope and independence

I read the mathematical arguments recovered from ChatGPT and archived as
`source/degree44-construction.md` and `source/same-assistant-validation.md`,
and inspected the supplied symbolic script recovered from that conversation.
I did **not** execute that script or import its implementation.
I wrote a fresh Python standard-library program using multivariate integer
polynomials represented by sparse dictionaries and division-free recursive
Laplace determinants. This differs from the supplied SymPy implementation and
does not depend on a stored matrix, numerical tolerances, or polynomial
truncation. The program ran successfully both normally and under `python3 -O`.

From the contribution directory
`references/webb-mf14-degree44-2026-09-17`, run:

```sh
python3 verification/verify_border_independently.py
python3 -O verification/verify_border_independently.py
```

The script writes a full exact `symbolic_certificate.json`. Captured output is
in `verification.log`.

## Audited algebra

Write

\[
Q=x^4+\alpha x^3,\qquad
R=aQ^2+bx^2Q+xQ+\eta x^3.
\]

For \(g=b-a\), \(\delta=b-2a\), and \(n=\eta-1+\alpha g\), the program
verifies identically in the polynomial ring over the integers that

\[
\bigl[\delta(aQ+gx^2)+(\delta-an)x\bigr]
\bigl[\delta(Q+x^2)+nx\bigr]
-gQ\delta^2-(\delta-an)nx^2=\delta^2R.
\]

Dividing by \(\delta^2\) recovers the claimed third-product identity. Both
factors use only \(x,x^2,Q\), already available after two products. Thus the
identity really costs one further product. For \(a=s^2,b=\gamma s\), the
denominator is \(s(\gamma-2s)\), nonzero for all sufficiently small nonzero
\(s\), including \(\gamma=0\).

Let \(V=\operatorname{span}(1,x,x^2,Q,R)\) and
\(W=\operatorname{span}\{uv:u,v\in V\}\). The monomials through degree six
lie in \(W\), using

\[
x^3=x\,x^2,\quad x^4=x^2x^2,\quad
x^5=xQ-\alpha x^4,\quad x^6=x^2Q-\alpha x^5.
\]

Every product of basis elements of \(V\) is in

\[
\mathbb C[x]_{\le6}+\operatorname{span}(Q^2,xR,x^2R,QR,R^2).
\]

The coefficient minor of the displayed twelve spanning vectors in rows
\(0,1,2,3,4,5,6,8,9,10,12,16\) is exactly \(a^5\), independently checked.
Consequently \(\dim W=12\) for \(a\ne0\).

For the map \(\Psi(u,v,w)=uv+w\), at \(u=R,v=Q+\lambda x^2\), the twelve
columns

\[
1,x,x^2,Q,R,
xv,x^2v,Qv,
xR,x^2R,QR,R^2
\]

are actual differential columns. Their determinant in the same coefficient
rows is exactly

\[
a^5\{\lambda-\eta-\alpha\lambda(b-a\lambda)\}.
\]

After \(a=s^2,b=\gamma s,\lambda=\eta+1\), it becomes

\[
s^{10}\{1-\alpha(\eta+1)[\gamma s-(\eta+1)s^2]\}.
\]

Its bracket tends to one. There is no exceptional fixed complex choice of
\(\alpha,\eta,\gamma\). The differential is onto \(W\), so the fourth
product's output is Zariski dense in \(W\). This addresses the crucial issue
that a sum of several products cannot simply be charged as one product.

## Entire coefficient degeneration

Use \(R_s=R|_{a=s^2,b=\gamma s}\) and

\[
(f_1,f_2,f_3,f_4,f_5)=(x^2R_s,Q^2,QR_s,R_s^2,xR_s).
\]

Define \(E_s\) by the 5-by-5 determinant with the coefficient rows
\(7,8,9,10\), followed by \((f_1,\ldots,f_5)\). I calculated all five
cofactors and the entire resulting polynomial. It has degree at most sixteen,
and degrees seven through ten vanish identically.

Here is a compact exact certificate for all remaining high coefficients.
If the cofactors of \(QR_s\) and \(R_s^2\) are \(s^2C\) and \(s^3D\),
respectively, direct expansion gives

\[
\begin{aligned}
C={}&-1-3\alpha\gamma s
 +(-2\alpha^3+9\alpha^2\gamma^2-6\alpha\eta-2\eta\gamma^2)s^2\\
 &+(-4\alpha^4\gamma+3\alpha^3\gamma^3+12\alpha^2\eta\gamma)s^3
 +(-8\alpha^6-4\alpha^5\gamma^2-10\alpha^4\eta)s^4,\\
D={}&2\gamma+(3\alpha^2-\alpha\gamma^2-\eta)s
 -8\alpha^3\gamma s^2+9\alpha^5s^3.
\end{aligned}
\]

The exact coefficient identities are

\[
\begin{aligned}
[x^{11}]E_s&=s^4\{3\alpha C+D[2\gamma+(6\alpha^2+2\eta+2\alpha\gamma^2)s+2\alpha^3\gamma s^2]\},\\
[x^{12}]E_s&=s^4\{C+sD[6\alpha+\gamma^2+6\alpha^2\gamma s+\alpha^4s^2]\},\\
[x^{13}]E_s&=s^5D(2+6\alpha\gamma s+4\alpha^3s^2),\\
[x^{14}]E_s&=s^6D(2\gamma+6\alpha^2s),\\
[x^{15}]E_s&=4\alpha s^7D,\\
[x^{16}]E_s&=s^7D.
\end{aligned}
\]

The fresh script verifies all these formulas against its cofactor expansion.
They prove exact divisibility, including parameter values where the generic
orders increase. Thus

\[
Z_s=-s^{-4}(E_s-\pi_{\le6}E_s)
\]

is polynomial in \(s\) and tends coefficientwise to

\[
x^{12}+(3\alpha-4\gamma^2)x^{11}.
\]

The projection here is only part of a linear combination in \(W_s\), since
\(\mathbb C[x]_{\le6}\subset W_s\). No actual circuit is being freely
truncated. The differential-density result is essential to making the use of
this linear combination valid.

The other eleven vectors

\[
1,x,\ldots,x^6,x^2R_s,Q^2,QR_s,R_s^2
\]

limit to a basis of \(\mathbb C[x]_{\le10}\) with determinant exactly one.
The script checks both their degrees and determinant. Hence constant linear
combinations of their approximating vectors supply any desired limiting
polynomial of degree at most ten.

For \(p_{12}\ne0\), choose
\(\gamma^2=(3\alpha-p_{11}/p_{12})/4\). This always has a solution over
\(\mathbb C\), so \(p_{12}Z_s\) matches the target's top two limiting
coefficients. Add a suitable lower combination. The case \(p_{12}=0\)
follows by applying the proved case to \(P+\epsilon x^{12}\) and using
closedness. No uniform bound on \(\gamma\) in \(\epsilon\) is needed for
that second, separate limit.

## Joint availability and continuation

For each admissible fixed \(s\), the same three-product circuit provides
\(x^2,Q,R_s\). One more product has dense outputs in \(W_s\), so the
closed simultaneous-output set \(\mathcal B_4\) contains

\[
(x^2,Q,R_s-\alpha Q,p)\qquad(p\in W_s).
\]

Because \(\eta=\beta+\alpha^2\), the third entry tends to
\(x^5+\beta x^3\). Zariski closed subsets of complex affine space are
Euclidean closed, so the coefficient limits proved above imply the desired
simultaneous quadruple. This is a valid joint argument, not a conclusion drawn
from separate availability statements for four polynomials.

For any fixed continuation parameters, the last three products and output
linear combination define a polynomial map \(T\) on all four degree-sixteen
inputs. On arbitrary such inputs the successive product degrees are at most
\(32,48,96\), so this is a map into the full degree-128 ambient space.
Polynomial-map continuity gives

\[
T(\mathcal B_4)\subseteq
\overline{T(\mathcal A_4)}^{Z}\subseteq\overline{\mathcal P_7}^{Z}.
\]

For clarity, the first inclusion follows because the inverse image under
\(T\) of the closed set on the right contains \(\mathcal A_4\), hence
contains its closure. No assumption that images of closed sets are closed is
used. High coefficients vanish at the limiting inputs by continuity; they
are never discarded.

## Review conclusion

All delicate steps survive an independent calculation and a separate logical
audit: the third-product identity, span dimension, differential minor,
absence of exceptional fixed parameters, full polynomial degeneration,
complex square-root choice, the zero-leading-coefficient case, joint
availability, and continuation in the full coefficient space. The determinant
degeneration and explicit minor are suitable for the manuscript and easier to
audit than the original Taylor-expansion presentation.

No correction to the mathematical border lemma is required. The final
degree-44 theorem additionally requires the separate nonsingular Jacobian
certificate, outside the scope of this review.

## Final standalone manuscript review

I subsequently read the complete standalone `proof.tex`, with particular
attention to Lemma 2, its proof, the continuation into the full ambient space,
and the appendix containing the explicit C,D cofactor formulas. The
mathematics in this final exposition agrees with the identities and logical
arguments audited above. In particular, every term and sign in both C,D
polynomials and all six high-degree coefficient formulas agrees with the
independently computed symbolic certificate.

The exposition explicitly distinguishes product-span linear combinations
from actual one-product outputs, explains the Euclidean limit inside a
Zariski-closed set, treats zero leading coefficients by a separate closure
argument, and retains the entire coefficient vector through continuation.
These details adequately address the potentially fragile steps of the
proof. The statement that a full-rank differential yields a Euclidean-open
subset by restriction to suitable affine directions is also correct.

I checked that the submitted
`verification/verify_border_independently.py` is byte-for-byte identical to
the independently written and successfully executed verifier reviewed here.
Its SHA-256 is
`711c459e9e9d543d5800753430fa40f3bb8fc5146a177ce8fcebf223ef7e4ff3`.

The final source incorporates the requested evidence-description correction:
the verifier expands the cofactors and assembles all of E_s. I checked this
wording and rechecked the appendix in the frozen source. No requested
correction remains outstanding within this review's scope.

### Frozen-source binding

This final-source review binds to
`references/webb-mf14-degree44-2026-09-17/proof.tex`, SHA-256:

```text
c987a6ac3532b50a8241702612c05d951d2a7d9b467a14aec922ea3c83d3de88
```

The hash was calculated directly from the final file on disk and agrees with
the source-freeze hash supplied by the preparing agent. **Final verdict:
PASS**, subject to the stated scope: the independent border construction and
continuation are accepted, while the separate degree-44 Jacobian and
external dimension theorem are covered by other evidence.
