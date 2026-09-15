# IE-17: independent final source referee 2

**Verdict: APPROVE the complete-target source candidate.** No mathematical, scope, proof, or attribution changes requested. **This is source approval, not authoritative Linux/Comparator approval or permission to promote status on this report alone.**

Reviewer: **OpenAI Codex AI agent `/root/existing_verification_audit`**, 2026-09-15. I independently reviewed the frozen statements before implementation and contributed no proof code. I cover fidelity, correctness, numerical correspondence, proof quality, reuse/API, documentation and attribution under the repository's Tau Ceti adaptation. This is neither external human peer review nor official Tau Ceti endorsement.

## Exact reviewed candidate and own checks

The complete candidate is identified by [final-source-inputs.json](final-source-inputs.json), SHA-256 `5c18abe144caa8ec8fcde682fb0d5ea959f2cdb3bca5da3844e1cfde923639db`. I independently recomputed all 21 recorded hashes, all ten pre-proof frozen input hashes, and the canonical/source hashes before and after my checks. All matched. The mathematical boundary remains the one approved before proofs at commit `5d9ae3c9`.

At sealing, I independently read local HEAD `0382f57e2d7da770563cc016b84fa3c89e086931`, which preserves this unchanged source candidate; the review report and its evidence are separate follow-up artifacts.

The [machine-readable review evidence](final-referee-2-evidence/review-evidence.json), SHA-256 `d418ebc90cff26a2242a6f72f7a78604e25b28f735cb14654010ed028b77ef42`, records every reviewed source, canonical source, frozen input, log and audit hash. In particular:

| File | SHA-256 |
| --- | --- |
| `NLA/IE17/Definitions.lean` | `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344` |
| `Challenge.lean` | `9a3b525a5925e97778fbdedd5a8b0ac40c28064752deb9c86b633459b545a6e5` |
| `NLA/IE17/LSMR.lean` | `143c528a8f7c8146edacdf7f67597921ff312aa84b3334cd7e4c67396e678a6b` |
| `NLA/IE17/Approximation.lean` | `3be2ec256ccd43aa39af538510f3d5a241c042a01325cd6a64667b67419a8afa` |
| `NLA/IE17/Proof.lean` | `9989cfdbaee9173434b76b5919627a91141d4bb492cf85b57ee0cdfdf35e1c68` |
| `Solution.lean` | `d305189e2b03335016e3828c172709b3de701c9efcf8f4962f4e41ea9c271007` |
| `README.md` | `ddcffeb80229fedc11d3306daf3caf97934dec7c15fdaadf8be042458eb77c41` |
| `formalization.yaml` | `4d4b001782e9342436dfa53f80edf921964cdbeb115a8d8204a9ddccd51b7791` |

I read every project proof module, the final wrappers, complete canonical README, complete original manuscript and numerical dossier. The unchanged analytic modules also have my detailed [norm/attainment review](final-referee-2-evidence/IE17-norms-interim.md) and [all-perturbation/certificate review](final-referee-2-evidence/IE17-optimal-interim.md). Those earlier limited verdicts are now supplemented by the full implementation review below.

My independent checks were:

- Copy the exact project sources into a new separate directory with no project build objects; run pinned Lean **4.33.1** `lake build Solution Challenge`. Every project module freshly compiled, exit **0**. [Build log](final-referee-2-evidence/fresh-build.log). The only eight warnings are the intentional Challenge specification placeholders. Pinned dependency objects were reused; this was a native local build, not Linux isolation or an independent dependency rebuild.
- Run my separate [FinalAudit.lean](final-referee-2-evidence/FinalAudit.lean), exit **0**: **29** explicit kernel-trust assertions and transitive axiom checks, including all **eight** public exports and the major intermediate semantic bridges. Every closure contains exactly `propext`, `Classical.choice`, `Quot.sound`. [Actual audit output](final-referee-2-evidence/final-axioms.log).
- Compare all eight final source type signatures with Challenge: exact textual matches. [Results](final-referee-2-evidence/signature-check.json). This is a supplementary source check, **not Lean4 Comparator**.
- Rerun my own pre-proof Fraction reconstruction from explicit A,b and original formulas. It independently derives the trajectory, full rational E, old and new positivity certificates, norms and both approximation fractions; all assertions pass and the result matches my pre-proof record. [Checker](final-referee-2-evidence/exact-check.py), [result](final-referee-2-evidence/exact-check.json). This arithmetic supports the review; it does not replace the quantified Lean proofs.
- Run the repository metadata validator myself using the existing `/private/tmp/nla-pr153-venv/bin/python`, exit **0**, all eight declarations covered. [Log](final-referee-2-evidence/metadata-validation.log). The first system-Python attempt lacked `jsonschema`; the existing validation environment resolved that environment issue.
- Inspect project imports and search proof-development sources for holes, new axioms, unsafe/native proof shortcuts and trust changes. There are no proof holes, no Challenge import in the solution closure, and no new axioms or native trust shortcut. The explicit LeanCert call uses kernel mode and is consumed by the proof.

## Full original-target correspondence

The complete canonical real rectangular problem is retained. `Vec n` is EuclideanSpace and `spectralNorm` explicitly uses the continuous linear map between Euclidean spaces. No ordinary function-vector sup norm, Frobenius norm or row-sum norm is substituted. The public norm theorem covers every real rectangular matrix and every real Euclidean test vector.

`Feasible` perturbs only A and keeps b fixed. Its residual sign is the negative of the displayed canonical normal equation and has exactly the same zero set. `errorSet` quantifies over **all real matrices E**, with no support, rank or rationality restriction. `IsOptimalError` is `IsLeast`, including actual attainment. The two general conjecture definitions retain arbitrary m,n,N,A,b and complete exact runs, and compare adjacent nonzero iterates. The refutation specializes a universal statement to one valid finite example; that is sufficient to settle each negative target.

`canonical_counterexamples` proves **both separate negations**, not merely the negation of their conjunction. It instantiates each universal claim at m=4,n=3,N=3 and adjacent indices 1,2, supplies the actual run and both nonzero witnesses, and contradicts the corresponding unsquared strict increase. The paired errors increase at the same pair of iterates. All original source cutoff chains are retained.

## Actual LSMR and termination

`isLSMR_of_normal_orthogonality` establishes the Pythagorean identity for every y in the full real Krylov submodule. Orthogonality is extended from generators by actual real-span induction. It proves global normal-residual minimization, not a comparison with finitely sampled candidates. Injectivity of H forces any tied minimizer to equal x, so the specified minimum-length convention follows without an unproved tie-breaking assertion.

For the literal integer A, the proof verifies its injectivity and H=diag(1,36,25). It verifies each exact iterate's Krylov membership using the displayed rational combinations of g,Hg,H²g. It checks normal orthogonality for k=1 and k=2 and the zero normal residual at k=3. The zeroth space and zero start are included. All three earlier normal residuals are nonzero; hence the proof really reaches **first** termination at three. The explicit x₁,x₂,x₃ are nonzero.

There is no extra hypothetical trajectory or a list merely called LSMR. The final theorem proves the frozen minimizing semantics for the actual complete list. This matches the canonical statement's explicit equivalent characterization of exact undamped LSMR.

## Actual spectral minima and all perturbations

`exists_optimal_error` proves feasibility nonempty using E=−A, closedness using the actual normal equation, and compactness of the spectral-norm ball intersected with the full feasible set. A minimizer in that ball is globally minimal: feasible matrices outside the ball have norm greater than its radius. This supplies a genuine attained minimum, including degenerate dimensions and zero inputs, without a hidden optimizer hypothesis.

For an arbitrary feasible perturbation at x₂, the nonzero new residual q is normalized only after proving its norm nonzero. Actual feasibility implies q is orthogonal to (A+E)x. The same unit direction u yields both Eᵀu=−Aᵀu and Ex=r−⟪u,b⟫u. The exact projection identity has the correct positive Ax term. Genuine operator bounds then control both quadratic forms. The q=0 branch is handled separately by Ex=r. These cases exhaust every feasible real E.

The upper certificate uses the complete rational perturbation from the original construction, checks its actual normal equation, and proves its every-real-vector squared norm bound through the reviewed congruence sum of squares. The lower certificate is likewise an identity for every real u using the reviewed positive weights. It gives the uniform 9901/10000 bound, including the separate consistent-perturbed branch. Divisions by ‖x₂‖² are justified by its strictly positive exact value.

`optimal_error_bounds` applies these bounds to the actual `IsLeast` values: the first compares to the explicit feasible E, and the second extracts and bounds the attaining E. It does not confuse a strict pointwise inequality with an infimum bound. The LeanCert kernel-certified cutoff chain supplies positivity and the strict gap used in these final comparisons.

## Literal Moore–Penrose approximation and uniqueness

`stackAt` is the actual 7×3 vertical stack [A;ηI]. Its Gram diagonal is (1+η²,36+η²,25+η²), strictly positive for every real η. The constructed `penroseAt=(KᵀK)⁻¹Kᵀ` is verified by **all four Penrose equations**, including both symmetry equations; the inverse is not merely asserted.

The generic `penrose_projection_unique` proves equality KP=KQ for any two matrices satisfying the Penrose laws. Consequently the projected-vector norm and `IsApproximation` value are unique, even though the definition deliberately uses a relation rather than a total pseudoinverse choice. Actual witnesses provide existence at both required iterates. There is no vacuity or dependence on an arbitrary generalized inverse.

`projection_norm_sq` expands the norm of the full Euclidean seven-vector, including the lower ηI coordinates, and proves the exact rational norm identity with positive denominators. Its absence of a direct r₃ term is correct because row four of A is zero; r₃ still contributes to **the full residual norm in η**. Both frozen residual norm values include that component. The final squares agree with my independently reconstructed exact source fractions.

`actualQ_approximation` supplies both x≠0 and normal residual≠0 before entering the nonterminal definition branch. For x₃, `terminal_errors_zero` instead uses the stipulated normal-residual-zero branch. Its raw residual is (0,0,0,1), so the proof correctly distinguishes an exact least-squares solution from a consistent solution. The optimal error at x₃ is also genuinely zero via feasible E=0 and norm nonnegativity.

The final unsquared inequalities use proved nonnegativity, so increasing squares are not mistaken for increasing signed values.

## Proof quality, reuse, documentation and attribution

The modules separate frozen meanings, general norm/geometry facts, finite data, certificates, algorithmic semantics, approximation and final exports. Names and comments identify their mathematical roles. General norm bounds, compactness and Euclidean APIs reuse pinned Mathlib; the relational Penrose lemma and full-span minimization criterion are reusable. The sparse diagonal inverse and signed-square identities avoid heavy eigensolver, general matrix-completion and spectral-minimum machinery without weakening the result. The existing Forsythe/Schiffer structure/API references are documented; no copied mathematical implementation or unproved source theorem is imported.

The complete original manuscript remains preserved, including its optional dense variant. That variant and the manuscript's generic completion theorem are not required exports for the canonical negative resolution; the actual complete counterexample and both original errors are fully proved. The new auxiliary certificate weights/congruence are identified separately from original authorship.

The canonical README, original manuscript and append-only problem registry are unchanged relative to the published base. ID **IE-17** and its canonical path are preserved. Metadata and code credit **George Stepaniants**, **Department of Computing and Mathematical Sciences, California Institute of Technology**, and retain **Matthew J. Colbrook** as the original counterexample author. No new contact email is supplied. The original source's historical contact information is preserved as part of that unmodified source.

The candidate README and metadata accurately describe local proof completion and still-pending final/operational gates. They disclose substantial AI assistance and independent non-implementing AI reviewers, without claiming external human review, author endorsement, novelty, measured costs or Tau Ceti endorsement. `sorry_count: 0` concerns proof development and explicitly excludes the eight specification-only placeholders. The unchanged default Lake target is still Challenge; the documentation prominently requires explicit `lake build Solution` and warns that Challenge alone establishes no proof. There is no hidden build-environment delta to approve.

## Remaining gate

**Complete-target source review PASS.** Every pre-proof semantic obligation is now discharged by actual proof code and my fresh local checks. No substantive finding remains open.

Fresh committed-input Linux isolation, Lean4 Comparator against the frozen Challenge with default kernel replay, its negative controls, provenance/source-hash binding and independent operational reviews are still required. This report claims none of those runs. Keep the canonical status **Solved** until those separate reproducibility gates pass and publication metadata is updated truthfully.
