# IE-17 exact LSMR trajectory — independent interim review

**Interim verdict: PASS for the completed `LSMR.lean` at the exact hash below.** Its closed witness theorem proves genuine minimization over every real Krylov competitor, the minimum-length convention, zero start, nonzero compared iterates, and first exact termination at step three. No statement weakening or algorithmic substitution was found. **This is not full-target approval or a Lean-verified status recommendation.**

Reviewer: OpenAI GPT-6 Codex `/root/reference_api_review` (independent AI), 2026-09-15. I did not author or modify the reviewed source. I read all of `LSMR.lean`, its actual imported project files, and the frozen definitions/source dossier, and performed the fresh compilation and trust audit described below.

## Exact reviewed inputs

- `NLA/IE17/LSMR.lean`: SHA256 `143c528a8f7c8146edacdf7f67597921ff312aa84b3334cd7e4c67396e678a6b`.
- Frozen Definitions: `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344`.
- NumericData: `3b325395a1ef8fa168261e4e0d3d146817bb1168778b8be4877f672c21fed495`.
- Norms: `c9af7b25650fd4873e6559794ed1a1c927ed38cda46bbbf987e323b8750d3137`.
- Geometry: `c22f2b3e1ddd53d462bf8860298591e814473ae05b59a5caa83c60f9c36f62b8`.

Challenge, Definitions, configuration and dependency files remain the pre-proof-approved bytes. I rehashed every source/config input copied into the independent test project against the authoritative worktree after the checks; all still matched. Full hashes appear in `/private/tmp/nla-ie17-lsmr-referee1/inputs.json` and `result.json`.

## Independent actual execution

I copied the required project sources into `/private/tmp/nla-ie17-lsmr-referee1/project`, with a fresh `.lake/build` and only the pinned dependency-package symlink. I used Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

- `lake build NLA.IE17.LSMR` exited **0**, completing **3644 jobs** with fresh compilation of Definitions, NumericData, Norms, Geometry and LSMR and no warnings.
- My separate `Audit.lean` imports LSMR and invokes `#check`, `#print axioms` and `#assert_trust kernel` for **all 13 public LSMR declarations**. `lake env lean Audit.lean` exited **0**.
- All 13 actual transitive axiom lists are exactly `propext`, `Classical.choice`, and `Quot.sound`. Private generator, membership, orthogonality and termination lemmas are covered transitively by the public closed witness theorem. There is no `sorryAx`, native-decision axiom, project axiom, or unproved run assumption in that closure.
- The printed type of `witness_run_exact` is the closed conjunction of `IsTerminatingLSMRRun witnessA witnessB witnessRun` and nonzero x₁,x₂,x₃, without hidden rank/orthogonality/membership hypotheses. The printed type of `witnessA_injective` is likewise closed.

Raw logs, audit source, all closure lists and source/evidence hashes are under `/private/tmp/nla-ie17-lsmr-referee1/`. `result.json` SHA256: `b0b4ab372a9adc27d34618f3f3d4de534364c121e9196f2b52f5c82a814b46d8`. These are actual local compilation/kernel-trust results, not a claim of authoritative Linux or Comparator execution.

## Mathematical and algorithmic fidelity

### Every real competitor and minimum length

The proof first establishes the exact identity

`normalResidual A b y = normalResidual A b x − (AᵀA)(y−x)`

using the actual Euclidean linear maps. The generic sufficient criterion `isLSMR_of_normal_orthogonality` takes membership of x, orthogonality against **the entire real Krylov subspace**, and injectivity of H=AᵀA. For any real competitor y in that subspace, y−x is in it as well. The proof applies Mathlib's real squared-norm identity to derive

`‖normalResidual y‖² = ‖normalResidual x‖² + ‖H(y−x)‖²`.

Norm nonnegativity gives global residual minimization. If a competitor has equal residual norm, the last square vanishes; injectivity of H gives y=x. Hence the minimum-length clause follows from actual uniqueness, rather than being dropped or separately assumed. Injectivity is a sufficient auxiliary hypothesis and is proved for the concrete witness; it is not inserted into the canonical universal monotonicity predicates or the closed run theorem.

`normal_orthogonality_of_generators` correctly extends each required generator identity through `Submodule.span_induction`, with zero, addition and **arbitrary real scalar multiplication** cases. It does not compare only basis vectors, rational coefficients or finitely sampled competitors. The original generator set remains exactly Hʲg for every natural j<k.

### Concrete iterates and first termination

The source proves the exact integer matrix's injectivity, computes H=diag(1,36,25), and proves H injective directly. It derives g=(11,6,5), Hg=(11,216,125), H²g=(11,7776,3125) from the actual witness matrix and vector. The three membership proofs use exactly the independently reviewed real coefficients:

- x₁ = `(1021/31201)g`;
- x₂ = `(16321/110438)g − (383/110438)Hg`;
- x₃ = `(961/900)g − (31/450)Hg + (1/900)H²g`.

These agree with my pre-proof independent 42-check Fraction reconstruction. The step-one and step-two normal equations are checked for all generator indices j<1 and j<2 respectively, then extended to the full real spans by the lemma above. Step zero uses the empty generator set, and the terminal step uses its proved zero normal residual. Explicit membership of x₃ is enough; proving the stronger equality K₃=ℝ³ or computing a Gram determinant inside Lean is unnecessary for this run theorem.

The exact normal residuals at x₀,x₁,x₂ are explicitly computed, and their first coordinates prove them nonzero. The normal residual at x₃ is proved zero. `witness_run_exact` checks every `Fin 4` index, including the initial and terminal indices, against the unchanged `IsTerminatingLSMRRun` definition. Its earlier-index condition covers steps 0,1,2; step 3 is excluded only by the impossible hypothesis `3<3`. This establishes **first** termination at 3, not merely that some listed point solves the least-squares equations.

All three nonzero iterates are established using their exact positive Euclidean squared norms. The terminal ordinary residual remains `(0,0,0,1)` by NumericData, so termination is correctly normal-residual zero rather than consistency. The compared iterates 1 and 2 are genuinely adjacent, nonzero and strictly before termination.

### Actual norms and imported definitions

`Vec n` remains `EuclideanSpace ℝ (Fin n)` throughout, and all normal residuals use the frozen matrix transpose and Euclidean linear maps. I read Geometry's `inner_eq_sum`, which derives real coordinate products from Mathlib's `PiLp.inner_apply` and `Real.inner_apply`; no different inner product or norm is introduced. The generic Pythagorean proof uses the actual L2 norms and inner product. No default matrix norm affects this algorithmic theorem.

## Proof quality, reuse and scope

The general minimization criterion and generator-to-span lemma are proved once and reused at all four steps. They use Mathlib's linear-map, norm/inner-product and submodule APIs. Finite coordinate arithmetic certifies the fixed witness; the proof does not formalize a larger numerical optimizer or add unnecessary eigendecomposition/Gram-system computations. The stronger whole-space injectivity hypothesis in the sufficient criterion is discharged concretely and does not narrow the actual original target. No general Krylov/LSMR declaration directly replacing these problem-specific obligations was located in the pinned library searches.

The file preserves Matthew J. Colbrook's original mathematical counterexample attribution and George Stepaniants's full Department of Computing and Mathematical Sciences, California Institute of Technology formalization credit, without a contact email. The formal proof uses the same canonical characterization of exact LSMR that was independently approved before implementation.

**Still pending for my complete-target approval:** the completed Moore–Penrose/approximation bridge, full optimal-error dependency chain and all eight final exports must be reviewed together; then the complete target must pass fresh permitted-axiom checks, independent final reviews and authoritative Linux Comparator verification against the frozen statements. This bounded interim result covers the LSMR component only.
