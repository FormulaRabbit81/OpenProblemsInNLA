# SP-05 — exact statement and proof preparation dossier

## 1. Stage, identity, and attribution

This is a pre-proof contributor dossier, not a final referee approval or a formal verification claim. The canonical status remains **Solved**. No Lean proof implementation is included. The six draft exports in §8 were read from the SP-05 project on 15 September 2026; they still require two independent approvals of the complete frozen inputs before proof implementation.

- Permanent ID: **SP-05**.
- Canonical page: `eigenvalues-and-inverse-problems/SP-05/README.md`.
- Source base inspected: published main `d8c38a795876b132c90df8d1be8682d3dcde394c`.
- Original affirmative proof: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom; manuscript prepared 11 September 2026.
- Planned formalization credit: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology; substantial OpenAI Codex assistance. Do not add a contact email. Preserve the original manuscript and its attribution verbatim.
- The source states that its original draft was generated in a ChatGPT conversation. Its historical independent Codex review is an agent review, not human peer review or a Lean certificate.

The immutable source hashes are in `reviews/initial/source-hashes.json` and are independently recomputed by `independent-exact-check.py`. The historically reviewed mathematical block starts at `## Theorem ` and ends before `## Scope and review notes`, with newline normalization and outer whitespace stripping. It has 3483 UTF-8 bytes and SHA-256 `54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42`, matching the original review.

## 2. Complete original target

Let n≥2 and let A,B∈ℝⁿˣⁿ be arbitrary symmetric positive definite matrices. Let T be the commutation matrix, characterized by T vec(X)=vec(Xᵀ), where vec stacks columns. Prove

\[
\min_{u\in\mathbb R^{n^2}\setminus\{0\},\ Tu=u}
\frac{u^T(A\otimes B)u}{u^Tu}
\;\leq\;
\min_{w\in\mathbb R^{n^2}\setminus\{0\},\ Tw=-w}
\frac{w^T(A\otimes B)w}{w^Tw}.
\]

The canonical equivalent formulation asks whether the smallest eigenvalue of J=A⊗B+B⊗A has a nonzero symmetric eigenmatrix under column vectorization. The source establishes the stronger statement that the minimizing eigenmatrix can be chosen positive semidefinite. The stronger theorem is meaningful for every n≥1, whereas the original two-sector comparison uses n≥2 so that the skew sector is nonempty.

The original reference gives this positive-definite comparison as Conjecture 1, equation (7), and uses column vectorization and the commutation matrix in the preceding setup. See the [primary author manuscript, arXiv:1805.09737v3](https://arxiv.org/html/1805.09737v3). This dossier does not make a new literature-completeness or priority claim.

### Scope that must survive formalization

Every real A,B and every integer n satisfying the stated hypotheses are included. No commutativity, common eigenbasis, eigenvalue simplicity, even dimension, rank restriction beyond positive definiteness, invertibility of a minimizing eigenmatrix, or rational-entry hypothesis is allowed. Repeated eigenvalues and singular minimizing eigenmatrices are included. Singular positive-semidefinite or indefinite **input** matrices are outside the original target. The n=0 case is excluded from the stronger nonzero-eigenmatrix assertion.

Both displayed minima must be attained minima of the actual full sectors. They must not be replaced by infima whose nonemptiness or attainment remains assumed. A finite numerical example is not the target.

## 3. Literal definitions in the current draft

`Mat n := Matrix (Fin n) (Fin n) ℝ`; `Vec n := (Fin n × Fin n) → ℝ`; `Operator n` is the square matrix on that product index. Product indices are ordered `(column,row)` in `Matrix.vec`. Their cardinality is exactly n²; using this product rather than `Fin (n*n)` is only an index convention.

- `columnVec X := Matrix.vec X`, so `columnVec X (j,i)=X i j`.
- `commutationMatrix n i j := if i = j.swap then 1 else 0` is the actual permutation matrix T, not an abstract predicate standing in for transposition.
- `frobeniusSq X := ∑ i, ∑ j, (X i j)^2`.
- `rayleigh K v := dotProduct v (K *ᵥ v) / dotProduct v v` is the literal real quotient. All value-set witnesses are required to satisfy v≠0, so its denominator is strictly positive.
- `jordanMatrix A B := Matrix.kronecker A B + Matrix.kronecker B A` uses Mathlib's actual Kronecker product.
- `sectorValues A B ε := {r | ∃ v, v≠0 ∧ T *ᵥ v = ε • v ∧ r = rayleigh (Matrix.kronecker A B) v}`.
- `skewExample n` has entry 1 at (0,1), −1 at (1,0), and zero elsewhere. Its definition uses the natural values of `Fin n` indices; n≥2 supplies the two distinct positions.

For a set S⊆ℝ, `IsLeast S a` means a∈S and a≤r for every r∈S. Consequently the two `IsLeast` predicates export actual nonzero minimizing vectors, as well as the universal comparison to every vector in their sectors. The positive-minimizer export explicitly gives a PSD nonzero eigenmatrix with positive eigenvalue μ and a lower bound against **every** nonzero real vector. Its eigen-equation and the positive denominator show its Rayleigh value equals μ; attainment is a consequence, not a missing premise.

Under this column convention, `(A⊗B) vec X = vec(B X Aᵀ)`, not vec(A X Bᵀ). For symmetric A,B, the sum J therefore represents X↦AXB+BXA, with its summands in the opposite order. This ordering is explicitly exported and tested diagnostically.

## 4. Complete mathematical proof plan and dependencies

### 4.1 Positive definite operator and inverse

Write L(X)=AXB+BXA on real matrices and extend it complex linearly. Use the actual Frobenius inner product `tr(X*Y)` on complex matrices, transported through column vectorization to the genuine Euclidean inner product. Do not infer a Frobenius norm from the ordinary Pi-function norm or the default operator norm on matrices.

The real and complex representations J are self-adjoint and positive definite. This follows directly from positive-definite Kronecker products and sums, or from

\[
\langle X,AXB\rangle=\|A^{1/2}XB^{1/2}\|_F^2>0\quad(X\ne0).
\]

Thus Φ=L⁻¹ exists, is self-adjoint and positive definite, and has real coefficients. L commutes with transpose; uniqueness of the inverse gives the same commutation for Φ. Its complexification is the actual inverse of the complexified L.

### 4.2 Inverse preserves the entire complex Hermitian PSD cone

The source uses a convergent exponential integral. A finite-dimensional proof of precisely the same property can avoid integration:

1. For a Hermitian PSD right-hand side Y, let X be the unique full complex solution L(X)=Y. Since L(X*)=L(X)*=Y, uniqueness proves X*=X. Hermitian symmetry is proved before any eigenvalue argument.
2. Put C=B⁻¹ᐟ²AB⁻¹ᐟ², X̃=B¹ᐟ²XB¹ᐟ² and Ỹ=B⁻¹ᐟ²YB⁻¹ᐟ². Positive definiteness of B gives all inverse and square-root cancellation identities, C≻0, X̃ Hermitian and Ỹ⪰0. Exact multiplication gives C X̃+X̃ C=Ỹ without A,B commuting.
3. If X̃ were not PSD, the complex Hermitian spectral theorem would supply a nonzero eigenvector v with real eigenvalue λ<0. Then
   \[
   \operatorname{Re}(v^*\widetilde Yv)
   =2\lambda\operatorname{Re}(v^*Cv)<0,
   \]
   because C≻0 and v≠0. This contradicts Ỹ⪰0.
4. Hence X̃⪰0; inverse congruence yields X⪰0.

The generic Sylvester fact used here is: if C is complex Hermitian positive definite, X is Hermitian, and C X+X C is PSD, then X is PSD. Invertibility and Hermitian symmetry of the required solution are separate proved bridges. Positivity merely on the real symmetric cone would be insufficient for the later use of iW.

This replacement proves the property actually used by the source and does not add a hypothesis. Neither the integral identity nor general exponential integration needs to become an exported obligation.

### 4.3 Real PSD eigenmatrix at the largest inverse eigenvalue

Let r>0 be the largest eigenvalue of Φ on the real Euclidean matrix space, and take a nonzero real eigenmatrix Z. The symmetric and skew parts `(Z+Zᵀ)/2` and `(Z−Zᵀ)/2` satisfy the same eigen-equation; at least one is nonzero. Call such a part W. Set H=W in the symmetric case and H=iW in the skew case. H is nonzero Hermitian and Φ(H)=rH.

Write H=P−N for its positive and negative parts, and |H|=P+N. P,N are Hermitian PSD and PN=NP=0. Actual Frobenius quadratic forms satisfy

\[
\langle |H|,\Phi(|H|)\rangle-
\langle H,\Phi(H)\rangle
=4\operatorname{tr}(P\Phi(N))\ge0.
\]

The sign uses complex PSD preservation plus `tr(PQ)≥0` for PSD P,Q. The latter follows by cyclicity from the PSD congruence P¹ᐟ² Q P¹ᐟ²; P and Q need not commute. The two cross terms agree by self-adjointness and Hermitian trace symmetry. Expanding the squares or using |H|²=H² proves equal **Frobenius** squared norms. `CFC.norm_abs` alone would not establish this because its norm is the C*-algebra operator norm.

The crucial realness step is mandatory. For real symmetric W it follows by real spectral calculus. For real skew W, H²=−W²=WᵀW is a real PSD matrix. Its real PSD square root, complexified, is also a complex PSD square root. Uniqueness of the complex PSD square root identifies it with |H|. This includes singular W and zero eigenvalues. One can unify both cases through H*H=complexification(WᵀW), then use the same uniqueness. A proof that complexification preserves real PSD matrices is needed, for example from their Gram factorization; it cannot be presumed by notation.

|H| is therefore a nonzero real PSD matrix. Its Φ-Rayleigh quotient is at least r. The universal upper bound for a real self-adjoint operator gives the opposite inequality. Equality implies the eigen-equation, including repeated extremal eigenvalues. Set μ=1/r. The inverse relation proves L(|H|)=μ|H|; reciprocal ordering of positive eigenvalues or an eigenbasis proves μ is a lower Rayleigh bound for every nonzero real matrix. This establishes the exact `positive_minimizer` export.

### 4.4 Full sectors, attained minima, and the final inequality

Prove Tᵀ=T, T²=I and T(A⊗B)T=B⊗A directly from the true permutation/vectorization. If Tv=εv, where ε=1 or −1, then

\[
v^TJv=2v^T(A\otimes B)v.
\]

Both sectors are real linear subspaces. The symmetric sector contains vec(I) for n≥1; the skew sector contains vec(skewExample n) for n≥2. Intersect each with the Euclidean unit sphere. The intersection is compact and nonempty, and the quadratic form is continuous, so it attains a minimum. Homogeneity of the Rayleigh quotient relates these minima to the full nonzero-vector sets in `sectorValues`. This proves both `IsLeast` predicates independently of the comparison.

The nonzero PSD matrix X from §4.3 is symmetric, hence its vector lies in the +1 sector. Its J-Rayleigh value is the global lower bound μ. The factor-two identity gives symmetric-sector least value μ/2, while every skew-sector value is at least μ/2. Combine with the attained skew minimum to conclude the exact original inequality.

## 5. Numerical trust and computation budget

The only proposed interval certificate is the exact rational fact `(0 : ℝ) < 2`, proved through LeanCert with explicit kernel trust. It must be consumed in the proof that the arbitrary-dimension `skewExample n` has positive Frobenius squared norm, using the exact identity `frobeniusSq (skewExample n)=2`. This proves the skew witness is nonzero and permits its normalization when establishing skew-sector minimum attainment. It is not an unrelated numerical decoration.

All n, matrix entries, eigenvalues, and cone arguments remain symbolic and universally quantified. No sampling, eigenvalue floating-point approximation, finite enumeration of matrices, interval enclosure of arbitrary spectra, expanded characteristic polynomial, or imported numerical answer substitutes for a theorem. Elementary rational algebra and exact finite sums can use ordinary kernel-checked tactics. Permit only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, new axiom, `native_decide`, or admitted analytic bridge in the final proof closure.

## 6. Exact optional diagnostics and reproduction

`independent-exact-check.py` uses only Python's standard library and `fractions.Fraction`. From the eventual Lean project directory, the portable retained command is:

```sh
python3 reviews/initial/independent-exact-check.py
```

The script discovers its enclosing repository by locating `problem_ids.json`. The external preparation copy also accepts an explicit repository-root argument. It prints deterministic JSON, without machine-dependent paths. These computations audit index conventions and source preservation; they prove no universal theorem and have no Lean trust status.

The noncommuting positive-definite example is

\[
A=\begin{pmatrix}2&1\\1&2\end{pmatrix},\quad
B=\begin{pmatrix}3&0\\0&1\end{pmatrix}.
\]

Their leading principal minors are (2,3) and (3,3). The diagnostic checks all four matrix units for the column-vectorization/Kronecker and transpose identities and checks TKT=B⊗A. For S=E₀₁+E₁₀ and W=E₀₁−E₁₀, it checks the factor-two identity and ‖W‖²_F=2. Their sampled K-Rayleigh values are both 4; these are explicitly **not asserted to be the sector minima**.

A second convention diagnostic takes C=A, X=diag(−1,2), Y=CX+XC=[−4,1;1,8], v=e₀, λ=−1 and checks vᵀYv=2λvᵀCv=−4. Here Y is deliberately not PSD: this only checks the sign identity behind the contradiction, not a counterexample to PSD preservation.

The deterministic JSON additionally records all seven canonical/source hashes and the preserved historical proof-block hash. All exact checks pass. The source documents, historical review, diagnostic output, and any independent future reviewer conclusions have distinct roles and must not be conflated.

## 7. Pinned Mathlib API plan

API names below were checked using a scratch file containing imports and `#check` commands only, against Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. `ApiProbe.log` records a successful exit. A listed library API is available infrastructure, not a proof of a missing project lemma.

| Required bridge | Pinned API or exact route |
|---|---|
| Actual column convention and bijection | `Matrix.vec`, `Matrix.vec_transpose`, `Matrix.vec_bijective`, `Matrix.vec_eq_zero_iff` |
| Actual Kronecker action | `Matrix.kronecker_mulVec_vec`; note argument order `(B⊗A) vec X = vec(A X Bᵀ)` |
| Frobenius/Euclidean inner product | `Matrix.vec_dotProduct_vec`, `Matrix.star_vec_dotProduct_vec`; explicitly transport to `EuclideanSpace` |
| Positive definite J and inverse | `Matrix.PosDef.kronecker`, positive-definite sum, `Matrix.PosDef.isUnit`, `Matrix.PosDef.inv` |
| PSD/PD congruences and trace signs | `Matrix.PosSemidef.conjTranspose_mul_mul_same`, `Matrix.PosDef.conjTranspose_mul_mul_same`, `Matrix.PosSemidef.trace_nonneg`, `Matrix.trace_mul_cycle` |
| Negative-eigenvector contradiction | `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`, `Matrix.IsHermitian.mulVec_eigenvectorBasis`, `Matrix.PosDef.re_dotProduct_pos`, `Matrix.PosSemidef.re_dotProduct_nonneg` |
| Real and complex spectral representations | `Matrix.IsHermitian.spectral_theorem`, `Matrix.IsHermitian.eigenvectorBasis`, `Matrix.IsHermitian.cfc_eq` |
| Square roots and inverse congruence | `CFC.sqrt_nonneg`, `CFC.sqrt_mul_sqrt_self`, `CFC.sqrt_unique`, `CFC.isUnit_sqrt_iff`; `Matrix.PosSemidef.inv_sqrt` in `Analysis/Matrix/Order` |
| Positive/negative parts | `CFC.posPart_nonneg`, `CFC.negPart_nonneg`, `CFC.posPart_sub_negPart`, `CFC.posPart_mul_negPart`, `CFC.posPart_add_negPart` |
| Modulus and its realness | `CFC.abs_sq`, `CFC.abs_smul`, `CFC.abs_eq_zero_iff`; PSD square-root uniqueness after proving complexification preserves PSD |
| Extremal eigenvector from equality | `IsSelfAdjoint.hasEigenvector_of_isMaxOn`; finite-dimensional spectral basis also provides an explicit weighted-average proof |
| Extremal eigenvalues available | `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`, `...hasEigenvalue_iInf_of_finiteDimensional` |
| Sector minima | Closed eigensubspace intersected with the compact Euclidean unit sphere; continuity plus actual normalization and quotient homogeneity |

Use the scoped Loewner matrix order from `Mathlib.Analysis.Matrix.Order` only where intended; there `0≤M` corresponds to actual `Matrix.PosSemidef`. An entrywise order would be wrong. No ready project-level theorem for complexification of PSD, the entire inverse-positive argument, or the realness of the modulus has been presumed. Those are explicit implementation obligations.

## 8. Exact correspondence to the six draft Comparator exports

The current `comparator.json` lists exactly these names, with challenge module `Challenge`, solution module `Solution`, and permitted axioms `propext`, `Classical.choice`, `Quot.sound`. The default proof target must never import `Challenge` to discharge an obligation. The source methods in §4 are internal supporting lemmas; they are not extra assumptions added to these signatures.

1. **`NLA.SP05.numerical_bound`**: `(0 : ℝ) < 2`. This exact certificate is consumed as specified in §5.
2. **`NLA.SP05.column_vectorization`**, for every n and arbitrary real A,B,X of size n: `(A⊗B)*ᵥcolumnVec X = columnVec(B*X*Aᵀ)`; `T*ᵥcolumnVec X = columnVec Xᵀ`; and `dotProduct (columnVec X) (columnVec X) = frobeniusSq X`. This establishes the actual conventions and Euclidean numerator/denominator interpretation.
3. **`NLA.SP05.skew_witness`**, every n≥2: `(skewExample n)ᵀ = -skewExample n`, `frobeniusSq (skewExample n)=2`, and `skewExample n≠0`. This proves nonemptiness in the complete dimension range, not just in n=2.
4. **`NLA.SP05.positive_minimizer`**, every n≥1 and arbitrary `A.PosDef`, `B.PosDef`: there exist μ∈ℝ and real X with `0<μ`, `X.PosSemidef`, `X≠0`, `jordanMatrix A B *ᵥ columnVec X = μ • columnVec X`, and `∀v, v≠0 → μ≤rayleigh (jordanMatrix A B) v`. This is the full stronger source theorem, with all real vectors in the lower-bound quantifier and an actual nonzero PSD eigenmatrix.
5. **`NLA.SP05.sector_minima`**, every n≥2 and arbitrary positive-definite A,B: there exist a,b with `IsLeast (sectorValues A B 1) a` and `IsLeast (sectorValues A B (-1)) b`. This includes attainment and universal minimality of both literal quotients.
6. **`NLA.SP05.canonical_result`**, the same complete hypotheses: there exist a,b satisfying both preceding `IsLeast` predicates and `a≤b`. This exactly resolves the entire displayed canonical claim.

The first three are concrete infrastructure/consumed numerical certificates. The fourth is stronger than the canonical target, as stated by the source. The fifth removes any ambiguity in the meaning of minimum. The sixth is the complete original theorem. There is no hidden premise that the inverse preserves positivity, that an extremal eigenmatrix is symmetric, or that sector minima already exist.

## 9. Source audit and conditions for completion

Reading the entire preserved mathematical block and historical review reveals no mathematical gap in the source route. The proposed integral-free inverse proof is valid on the full complex Hermitian cone once the explicitly listed existence, uniqueness, and Hermitian-symmetry steps are proved. The source's informal positive dimension convention is made exact by n≥1 in its stronger export; the original n≥2 target is unchanged.

The hardest remaining implementation obligations are complexification with PSD preservation, modulus realness, actual Frobenius variational reasoning, and the inverse extremal-eigenvalue correspondence. These are proof work, not reasons to weaken the boundary. The prototype API probe and finite diagnostics are not evidence that they have already been formalized.

Completion requires two independent approvals of the exact pre-proof statement bytes, full kernel-safe proof closure for all six exports, Lean4 Comparator against those independently reviewed signatures, successful pinned reproducible builds, kernel LeanCert consumption, all permitted-axiom checks, and independent final source-to-formal correspondence reviews. Linux/CI success and publication must be recorded only after actual execution. Preserve IDs, all source statements and attributions, prior verifications, and historical review files. This dossier alone authorizes no status promotion.
