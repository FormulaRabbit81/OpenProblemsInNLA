# NM-04: complete statements before Lean implementation

The exact mathematical plan was recorded before Lean source was written;
the sealed original is in `precode-01`. The current stage has concrete
Definitions and 35 independent Challenge statements only. No proof, numerical
certificate execution, local elaboration, statement freeze, Comparator run,
or independent statement approval is claimed. Five analytic auxiliaries in
Challenge allow zero rows as well; the canonical theorem retains every
original positive dimension and positive matrix. The coercivity contract
uses a positive entrywise lower bound, which itself implies entry positivity.

The original solution is Matthew J. Colbrook's Theorem 1, Sections 1–4 of
`NM-04_sinkhorn_identity.tex`, preserved from upstream commit
`849003686970b372e1b2128ba072f86168f81d38`. The question is attributed to
Eric Rowland and Jason Wu. George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, is the contributor
for this proposed formalization, with substantial OpenAI Codex assistance.
This preparation does not transfer authorship of the original mathematics.

## The final target, without additional assumptions

For **every** natural number `m,n` with `1 ≤ m` and `1 ≤ n`, and **every**
matrix `A : Matrix (Fin m) (Fin n) ℝ` whose entries are strictly positive,
let `S = Sink(A)` denote the unique positive diagonal scaling of `A` with
every row sum equal to `1` and every column sum equal to `ρ = (m:ℝ)/(n:ℝ)`.
The existence and matrix uniqueness of this scaling must be proved, not
assumed. Set `x = S 0 0`, with the two zero indices supplied by the positive
dimension hypotheses.

The public index set is exactly

\[
 D=\{(R,C):R\subseteq\{2,\ldots,m\},\ C\subseteq\{2,\ldots,n\},\ |R|=|C|\}.
\]

Use the increasing order of the original row and column indices. Empty
determinants and products equal `1`. For `I=(R,C)` define

\[
 \Delta_A(I)=\det A_{\{1\}\cup R,\{1\}\cup C},\qquad
 \Gamma_A(I)=a_{11}\det A_{R,C}.
\]

For any finite ordered set `U` and member `s`, its position is the **one-based**
integer `pos(s,U) = 1 + |{t∈U : t<s}|`. The integer matrix `H` on all of `D`
has diagonal

\[
 H_{I,I}=|R|\bigl((m:\mathbb Z)+(n:\mathbb Z)\bigr)
          -(m:\mathbb Z)(n:\mathbb Z).
\]

Subtraction is in `ℤ`; it must never be truncated natural-number subtraction.
For distinct `I=(R,C)` and `J=(R',C')`, put
`τ=(R\R',R'\R,C\C',C'\C)`. The four off-diagonal cases are exactly:

| `τ` | `H I J` |
|---|---|
| `(∅,{s},∅,{t})` | `(-1)^(pos(s,R')+pos(t,C')) * m` |
| `({s},∅,{t},∅)` | `(-1)^(pos(s,R)+pos(t,C)+1) * n` |
| `(∅,∅,{s},{t})` | `(-1)^(pos(s,C)+pos(t,C')) * m` |
| `({s},{t},∅,∅)` | `(-1)^(pos(s,R)+pos(t,R')) * n` |
| every other off-diagonal configuration | `0` |

For each `E : Finset D`, restrict the **real cast** of `H` simultaneously to
rows and columns in `E`; the determinant of this principal submatrix does not
depend on the enumeration of `E`. The final theorem is the exact scalar identity

\[
 \boxed{\quad
 \sum_{E\subseteq D}
   \det\bigl((m:\mathbb R)^{-1}H_E\bigr)
   \left(\prod_{I\in E}\Delta_A(I)\right)
   \left(\prod_{I\in D\setminus E}\Gamma_A(I)\right)
   x^{|E|}=0.\quad}
\]

Every coefficient and every subset is retained. There is no genericity,
nonvanishing-minor, rank, integrality, square-dimension, or size-bound
hypothesis. The expression may be the zero polynomial at a degenerate positive
matrix; nontriviality of the polynomial is not a requirement of NM-04.

## The only planned numerical certificate

Set the exact rational `h = (1:ℝ)/2`. The complete numerical certificate is

\[
             0<h\quad\text{and}\quad h<1.
\]

Use `interval_decide (trust := kernel)` for these two ground rational
inequalities and consume the named result in the coercivity proof below:
`κ = h * ((m:ℝ)/(n:ℝ))` is positive and is at most `m/n`. Its positivity and
upper bound must be referenced by the proof, not left as an unused import.
All transcendental estimates, dimension dependence and determinant identities
are symbolic. No floating-point data, subdivisions, sampled dimensions,
approximated exponentials/logarithms, or interval box over matrix entries is
required.

The seven rational matrices in the earlier triage packet are convention
diagnostics only. They are not this numerical certificate, a proof of the
universal result, or a formal-verification result. Their stored output was
read, not independently executed by this preparer.

## Actual scaling: the complete analytic obligations

For `t : Fin n → ℝ` and positive `A`, define concrete functions

\[
 Z_i(t)=\sum_j A_{ij}e^{t_j},\qquad
 F_A(t)=\sum_i\log Z_i(t)-\rho\sum_j t_j,
\]
\[
 g_j(t)=\sum_i\frac{A_{ij}e^{t_j}}{Z_i(t)}-\rho,
 \qquad V=\{t:\sum_jt_j=0\}.
\]

Prove all the following, for arbitrary positive dimensions and positive `A`.

1. Every `Z_i(t)>0`, and `F_A` is continuous on the whole real vector space.
   For every `t,d`, the actual one-variable function `s ↦ F_A(t+s d)` has
   derivative at `0` equal to `Σ_j d_j g_j(t)`.
2. If `a>0` and `a≤A_ij` for every entry, then for every `t∈V`,
   \[
       F_A(t)\ge \kappa\|t\|_\infty+(m:\mathbb R)\log a,
       \qquad \kappa=\tfrac12(m:\mathbb R)/(n:\mathbb R)>0.
   \]
   Here the function-space norm is Mathlib's ordinary finite-product sup
   norm; it is an auxiliary norm, not a replacement for any target matrix
   norm. The proof takes `q=max_j t_j`, proves `q≥0` and `‖t‖∞≤n q`, and
   uses `Z_i≥a exp q` and monotonicity of `log`. It first obtains the stronger
   coefficient `m/n`, then consumes `h<1` to obtain the displayed coefficient.
3. Obtain such an `a` from the attained minimum of the finitely many positive
   entries of `A`. Write `c=m log a` and
   \[
       R=(1+|F_A(0)-c|)/\kappa>0.
   \]
   Outside the radius-`R` closed ball in `V`, coercivity gives `F_A(t)>F_A(0)`.
   The intersection of the closed ball and `V` is compact, contains `0`,
   and has a minimum of `F_A`. Thus a global minimizer `t₀∈V` exists.
4. At this actual minimizer, apply the derivative assertion to
   `d=e_j-e_0`. These are genuine mean-zero lines, including the zero
   direction when `j=0`. Fermat's theorem gives `g_j(t₀)=g_0(t₀)`.
   Since `Σ_j g_j(t)=0` for every `t`, every `g_j(t₀)=0`.
5. Define positive factors `β_j=exp(t₀_j)` and `α_i=1/Z_i(t₀)`.
   Then `S_ij=α_i A_ij β_j` has row sums `1`, column sums `ρ`, and all entries
   positive. The proof can also observe `∏β_j=1`, but neither this gauge nor
   uniqueness of individual diagonal factors is part of the final target.
6. Prove matrix uniqueness. If positive balanced `S,T` lie in the same
   positive scaling orbit, write `T_ij=u_i S_ij v_j` with `u_i,v_j>0` and let
   `vmax=max_j v_j`. Row sums force `u_i≥1/vmax`. The balanced column at a
   maximum index, with strictly positive weights, forces equality for every
   `u_i`. The balanced rows then force `v_j=vmax` for every `j`. Hence `T=S`.
   Apply this to two scalings of `A`; do not assert uniqueness of `α,β`
   individually, since their common scalar gauge is real.
7. The concrete total choice called `sinkhorn A` is proved to have precisely
   these existence, positivity, scaling and margin properties. Prove that
   every balanced positive scaling of `A` equals it. The canonical README
   explicitly defines the Sinkhorn limit equivalently by this unique matrix;
   a new alternating-normalization convergence theorem is therefore outside
   this target, and is not claimed.

## Universal algebra: no inverses of minors

For arbitrary finite ordered row and column index types (empty allowed), a
real matrix `T`, and equal-cardinality subsets `I=(R,C)` of size `k`, let
`f_I(T)` be its actual sorted submatrix determinant. Define the cofactor form
using the actual adjugate of that `k×k` submatrix:

\[
 D_I(T;Z)=\sum_{a,b=0}^{k-1}
       (\operatorname{adj} T_{R,C})_{b,a}\,Z_{R_a,C_b}.
\]

This is a concrete finite polynomial expression. Its use as a cofactor form,
and its relation to signed deleted minors, are proved. It is not declared to
be a derivative by an assumption. If `k=0`, the sum is empty and equals `0`.

For a minor array `f`, define `L,U,C₀,R₀` by the four signed transition sums
displayed in Section 2 of the source: deletion of one row and one column;
addition of one row and one column; exchange of one column; exchange of one
row. Positions are exactly the one-based positions above. The planned generic
transition coefficient definitions and their literal support contracts are
specified in `SEMANTIC-PLAN.md`.

Prove the universal rank-one update and universal bordered identity:

\[
 f_I(T+zuv^{\mathsf T})=f_I(T)+zD_I(T;uv^{\mathsf T}),
\]
\[
 a\,\operatorname{adj}(V)\,b
     =d\det V-\det\begin{pmatrix}V&b\\a&d\end{pmatrix}.
\]

They hold even when `V` is singular or empty. Use alternating multilinearity
and existing cofactor formulas; the pinned Schur-complement lemma that
assumes `IsUnit V.det` is insufficient. Terms with two replaced proportional
columns have determinant zero. No division by `det V`, `Δ`, or `Γ` is legal
in this route.

With `J` the all-ones matrix, `r=T1`, `cᵀ=1ᵀT` and `s=Σ_ij T_ij`, prove
the four exact identities:

\[
\begin{aligned}
D_I(T;J)&=(Lf)_I,\\
D_I(T;r1^{\mathsf T})&=k f_I+(C_0f)_I,\\
D_I(T;1c^{\mathsf T})&=k f_I+(R_0f)_I,\\
D_I(T;rc^{\mathsf T})&=s f_I-(Uf)_I.
\end{aligned}
\]

The last identity at `k=0` is `0=s(T)-Σ_ij T_ij`; it must remain covered.
The exchange signs include sorting the replacement into the original order.

## Balanced null vector and the exact coefficient formula

For any already balanced positive `S`, split off its first row and column:
`S=[[x,rᵀ],[c,B]]`, and let `T=B-crᵀ/x`. Since `x>0`, only this scalar
division needs a nonzero hypothesis. Prove

\[
 T1=1-c/x,\quad 1^{\mathsf T}T=\rho(1^{\mathsf T}-r^{\mathsf T}/x),
 \quad s(T)=m-\rho/x.
\]

For every `I` of size `k`, prove `Δ_S(I)=x f_I(T)`. Use the rank-one update,
the four identities and the margin equations to obtain the full relation

\[
 m\det B_{R,C}+[k(m+n)-mn]\Delta_I
 +n(U\Delta)_I-m(L\Delta)_I+m(C_0\Delta)_I+n(R_0\Delta)_I=0.
\]

Define `w_I=((n:ℝ)/(m:ℝ))^k` and

\[
 K(A,z)=\operatorname{diag}\Gamma_A
           +(z/(m:\mathbb R))\,H_{\mathbb R}\operatorname{diag}\Delta_A.
\]

Prove the transition-weight action with the actual `H`: raising changes
`m` to `n`, lowering changes `-n` to `-m`, exchanges preserve the weight.
Then prove `K(S,x)w=0` and `w_empty=1`, so `w≠0`.

For an arbitrary positive diagonal scaling `S=diag α A diag β`, define

\[
 d_I=\alpha_1\beta_1\prod_{i\in R}\alpha_i\prod_{j\in C}\beta_j>0.
\]

Prove both `Δ_S(I)=d_I Δ_A(I)` and `Γ_S(I)=d_I Γ_A(I)`, and therefore, for
every real `z`, `K(S,z)=K(A,z)diag d`. Choosing the actual `S=Sink(A)` gives
the nonzero null vector `(diag d)w` for `K(A,x)`, with a strictly positive
empty coordinate.

Finally prove the general weighted principal-minor expansion

\[
 \det(\operatorname{diag}\gamma+zM\operatorname{diag}\delta)
 =\sum_{E\subseteq D}\det M_E
    \prod_{I\in E}\delta_I\prod_{I\notin E}\gamma_I\ z^{|E|}
\]

for every finite index type `D`, arbitrary real `M,γ,δ,z`, including an
empty index type and zero diagonal factors. Apply it to
`M=(m:ℝ)⁻¹ H_ℝ`. The nonzero null vector implies `det K(A,x)=0`, proving
the final displayed coefficient formula exactly.

## Boundary obligations and scope

- `m=1`, `n=1`, and `m=n=1` are included. Tail index types can be empty;
  their subset-pair index `D` still contains `(∅,∅)`.
- The empty minor has value `1`; `Δ_empty=Γ_empty=a₁₁`; `w_empty=1`.
- A positive rank-one matrix and any other vanishing-minor pattern are
  included. No cancellation by a minor is used.
- The row/column margin ratio is `m/n`, while the null-vector base is `n/m`.
- Matrix uniqueness is proved; diagonal-factor uniqueness is not claimed.
- The literal four signs and the `m` versus `n` weights are separate checked
  contracts, not inferred from a small numerical example.
- Only the canonical Theorem 1 is in scope. The source's arbitrary margins,
  exterior-power interpretation, coefficient-sum symmetries, and algebraic
  degree consequences are not additional completion claims.
