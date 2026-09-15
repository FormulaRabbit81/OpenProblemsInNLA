# IE-15: independently reviewed mathematical and numerical targets

## Frozen source and scope

Base: `c7f399b1694e0a68756e8d060e2a71775c044301` on published `origin/main`, read from `/private/tmp/nla-formalization-campaign-20260915`.

Canonical path: `linear-systems-and-elimination/IE-15/README.md`.

Written proof inspected in full: `linear-systems-and-elimination/IE-15/solution.md`, Theorem 1 and Sections 1–5. Source SHA-256 values are recorded in `reviews/initial-source-hashes.json`.

Original proof attribution: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Retain the earlier conjecture/source attribution to Higham and the contextual references to Edelman–Urschel and Shah–Urschel. The formalization should add no contact email.

This dossier is an independent informal mathematical and scope review performed before new Lean proof implementation. It approves the written target and analytic argument as a basis for formalization. It does not certify a future Lean definition, prove a kernel theorem, substitute for a second independent reviewer, or authorize a status promotion.

## 1. Exact canonical target

All matrices and arithmetic are real and exact. For each order `n ∈ {3,4}`, quantify over **every** nonsingular matrix `A : Matrix (Fin n) (Fin n) ℝ`, and **every** admissible rook-pivoting path from `A`.

At a stage with active order `d ≥ 1`, a rook choice is a pair of active indices `(r,c)` whose entry `p` is nonzero and satisfies

```math
|S_{rj}|\le |p|\quad(0\le j<d),\qquad
|S_{ic}|\le |p|\quad(0\le i<d),\qquad p=S_{rc}\ne0.
```

These are non-strict inequalities. Every tie is allowed. There is no requirement that the pivot be maximal over the entire active matrix, and no particular pivot-search implementation is part of the target.

Move the selected row and column to the first positions by permutations. For the resulting matrix `S'`, the next active matrix has entries

```math
S^{\mathrm{next}}_{ij}=S'_{i+1,j+1}
 -S'_{i+1,0}S'_{0,j+1}/S'_{00}\quad(0\le i,j<d-1).
```

A full path includes every active matrix of orders `n,n−1,…,1`. Permuting the remaining active indices only relabels future choices and does not restrict the set of paths. Nonsingularity of the original matrix, the nonzero pivots and Schur-complement identities must be connected formally; never replace the original nonsingularity hypothesis by an unproved assertion that a preferred path exists.

Define

```math
\|S\|_{\max}=\max_{i,j}|S_{ij}|,\qquad
\rho(A,\pi)=\frac{\max_{S\text{ in }\pi}\|S\|_{\max}}
 {\|A\|_{\max}},
```

and define `g_RP(n)` as the supremum of these growth ratios over all real nonsingular `A` and all their admissible paths. The initial matrix belongs to the maximum. Every intermediate active entry belongs to the maximum; a maximum of pivot values alone is not the target. Since `A` is nonsingular and `n≥1`, its maximum absolute entry is positive.

The complete theorem is the conjunction

```math
g_{\mathrm{RP}}(3)=3\quad\text{and}\quad
g_{\mathrm{RP}}(4)=14/3.
```

A transparent equivalent theorem package consists of:

1. For every admissible order-three instance, every active entry has absolute value at most `3 * ‖A‖max`.
2. For every admissible order-four instance, every active entry has absolute value at most `(14/3) * ‖A‖max`.
3. The order-three witness below is nonsingular, has an admissible path and attains ratio `3`.
4. The order-four witness below is nonsingular, has an admissible path and attains ratio `14/3`.
5. Deduce both canonical supremum equalities from 1–4 using the actual supremum definition, including nonemptiness and boundedness as required by the chosen Lean supremum API.

The four bounds/witnesses may serve as intermediate declarations. The public target should expose the full conjunction of supremum equalities or a formally proved equivalent complete characterization, not only one dimension, one chosen path or the scalar lemma.

## 2. Exact witness data

Zero-based formal indices correspond to the manuscript's one-based rows and columns. The witness path always chooses the first row and first column, with no swaps.

### Order three

```math
A_3=\begin{pmatrix}1&0&-1\\0&1&-1\\1&1&1\end{pmatrix},
\quad S_2=\begin{pmatrix}1&-1\\1&2\end{pmatrix},
\quad S_3=(3).
```

- Pivots: `1,1,3`.
- Stage maximum absolute entries: `1,2,3`.
- `det A₃ = 3 ≠ 0` and `‖A₃‖max = 1`.
- All chosen pivots are maximal in their own active row and column.
- The growth is exactly `3`.

### Order four

```math
A_4=\begin{pmatrix}
1&0&1&1\\
0&1&1/3&-1\\
-1/3&-1&1&-1\\
-1&1&1&1
\end{pmatrix},
```

```math
S_2=\begin{pmatrix}1&1/3&-1\\-1&4/3&-2/3\\1&2&2\end{pmatrix},
\quad S_3=\begin{pmatrix}5/3&-5/3\\5/3&3\end{pmatrix},
\quad S_4=(14/3).
```

- Pivots: `1,1,5/3,14/3`.
- Stage maximum absolute entries: **`1,2,3,14/3`**. The universal rough bound `4` after two eliminations is not this witness's stage maximum.
- `det A₄ = 70/9 ≠ 0` and `‖A₄‖max = 1`.
- All chosen pivots are maximal in their own active row and column, including the `±5/3` ties at the third stage.
- The growth is exactly `14/3`.

All values are rational. No decimal approximation, eigensolver, interval subdivision or exhaustive continuous optimization is needed for these witness facts. The independent Python `Fraction` reconstruction is recorded in `reviews/initial-rational-reconstruction.json`; it is a pre-proof check, not a kernel certificate.

## 3. Analytic upper-bound obligations

The proof reduces arbitrary admissible paths to normalized elimination coordinates

```math
A=L\,\operatorname{diag}(p_1,\ldots,p_n)R,
\qquad |A_{ij}|\le1,
```

where `L` and `R` are unit triangular and all strict triangular multipliers have absolute value at most one. A formal reduction must prove that these bounds are equivalent to the active rook conditions for the fixed diagonal path and that moving a full path's eventual permutations to the outset reproduces its active matrices up to permutations.

Row sign changes make all pivots positive; subsequent simultaneous row/column sign changes make `L_ni ≥ 0` for all `i<n`. The exact identity behind the first operation is

```math
S A=(SLS)(SD)R,\qquad S=\operatorname{diag}(\operatorname{sign}p_i).
```

All changes preserve entry absolute values and growth. Replacing the normalized bottom-right original entry by `1` leaves earlier pivots and their active rows and columns unchanged, increases the positive final pivot by `1−A_nn`, and retains nonsingularity. This replacement is used only to bound the final pivot; prior-stage bounds must still refer to the original path.

The normalized first pivots satisfy `0<p₁≤1` and `0<p₂≤1+p₁≤2`. Every entry after one elimination has absolute value at most `2`; every entry after two has absolute value at most `4`. Consequently the final-pivot bounds `3` and `14/3`, together with those intermediate bounds, establish the required all-entry growth bounds.

For order three, with the manuscript's normalized variables, the final value is `1+pcd+qef`. If this were greater than `3`, then `d,f>0`, `qe>1`, `qf>1`. The original `(2,3)` and `(3,2)` bounds force `a,b<0`, contradicting `|q+pab|≤1`. The same final two-step Schur-value bound applies to a possibly singular three-by-three matrix whose first two pivots are nonzero and rook-admissible; handle final value zero separately and a negative final value by a last-row sign change. This extension is needed for the principal submatrix `{1,2,4}` in the order-four argument.

### Required scalar lemma

Define `h(c,d)=3cd+1+|c−d|`. For real variables satisfying

```math
0<p\le1,\quad q>0,\quad -1\le a,b,d_1,d_2\le1,
\quad 0\le c_1,c_2\le1,
```

```math
|q+pab|\le1,\quad |qd_2+pa d_1|\le1,
\quad |qc_2+pc_1b|\le1,
```

prove

```math
p h(c_1,d_1)+q h(c_2,d_2)\le8.
```

Every hypothesis and all signed cases matter. In particular `d₁,d₂` may be negative; silently replacing them by nonnegative variables weakens the required upper-bound argument.

The manuscript's proof splits `q≤1` from `q>1`, then the signs of `a,b,d₁,d₂`. Its final case uses

```math
\Phi(q,U,V)=2q+2\min\{q,U,V,UV/q\},\qquad q,U,V>0,
```

and its monotonicity in each positive variable. That monotonicity has an elementary algebraic proof from the three regions determined by `min(U,V)` and `max(U,V)`; no analytic differentiation is necessary in Lean. This avoids unnecessary numerical computation without modifying the lemma.

For order four, put `W=p₁c₁d₁+p₂c₂d₂`. The principal-three-by-three argument gives `W≤2`. If `c₃=0` or `d₃≤0`, the final pivot is at most `3`. Otherwise take `C=c₃`, `D=d₃` in `(0,1]`. The original `(3,3),(3,4),(4,3)` entries yield the bilinear bound in manuscript equations (12)–(13). Separate convexity reduces the auxiliary expression to four corners whose upper bounds are `6,10,10,11`; the last corner is `3+p₁h(c₁,d₁)+p₂h(c₂,d₂)≤11`. This gives final pivot `1+11/3=14/3`.

The convexity argument can be proved directly by bilinear interpolation/corner weights and maxima of four affine functions. It must not be implemented as an unproved optimizer output. The finite corner reduction is exact and includes the whole `[0,1]²` domain.

## 4. Independent review conclusion

**PASS for the complete written mathematical argument and the exact numerical transcription above.** I read all five proof sections and independently checked normalization, permutation and sign invariance, the singular-three-by-three submatrix extension, every sign case in the scalar lemma, the monotonicity formula for `Φ`, and the separately convex four-corner bound. I independently reconstructed both witness elimination paths with rational arithmetic and obtained exactly the stated matrices, determinants, row/column rook inequalities and growth ratios. I found no material mathematical gap in this written argument.

This result remains **Solved** until two separately reviewed Lean statements, their correspondence to this full canonical model, complete proofs, reproducible kernel verification, Comparator results and permitted-axiom checks have all passed. The current review is an informal AI-agent review, not external human peer review or Lean verification.

## 5. Proposed Lean boundary

`NLA/IE15/Definitions.lean` uses zero-based `Fin n` indices and the existing IE-05 padded-trajectory convention, adapted to a pair of rook row/column choices. `pivotSwap` performs exactly the two selected interchanges. `schurStep` zero-pads entries outside the new trailing block. `AdmissiblePivot` requires both selected indices active, a nonzero pivot, and non-strict row and column inequalities. `AdmissiblePath` checks every stage. No search strategy, global maximum condition, positive-pivot premise or normalization premise is imposed on the exported theorems.

`entryMaxNN` and `activeMaxNN` are finite maxima of nonnegative real absolute values; `growth` includes all n stages. `growthSet` additionally requires the original determinant to be nonzero. `rookGrowthSup` is the actual real `sSup`. The eight declarations in `Challenge.lean` include maximum semantics, both universal all-entry bounds, both exact witnesses, both greatest-element assertions and the conjunction of the two supremum equalities. The greatest-element assertions explicitly prevent a claim based only on the totalized real supremum of an empty or unbounded set.

The challenge contains eight deliberate specification placeholders. They are not proofs. No `Solution.lean` exists at this pre-proof stage. The independent statement reviewers must inspect the exact definitions and signatures, and subsequent edits to this mathematical boundary require renewed review.
