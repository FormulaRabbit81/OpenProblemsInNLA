# KE-05 final independent referee 1

**Verdict: PASS for mathematical fidelity and local kernel proof closure.** No blocking correction requested. Actual isolated Linux Comparator and its rejection/isolation controls remain a separate gate; this report does not certify them or authorize a claim that they ran.

Reviewer: `/root/iv06_statement_referee_1`, AI agent, independent nonauthor of KE-05's boundary and implementation. I subsequently reused KE-05's `RegularAt` framework with attribution in IE-04; I did not author or edit KE-05. This review applies `docs/lean/REVIEW.md`'s Tau Ceti adaptation, not official Tau Ceti or human peer-review endorsement. I independently read the complete canonical problem and Stepaniants manuscript, numerical plan, frozen definitions/Challenge, all 21 active NLA modules and Solution, proof notes, metadata and actual library APIs. No historical approval substitutes for those reads.

## Scope and fidelity

The ten exports retain the full universally quantified probabilistic conjecture: arbitrary positive block size, at least two blocks, every admissible real diagonal data family, all confidence levels and a constant independent of the deterministic spectral data. `Admissible` separates spectra between blocks; it does not prohibit repeated eigenvalues within a block or interlacing between blocks. The counterexample at b=2,d=3 suffices to negate the universal statement. It does not refute a conjecture restricted to ordered disjoint spectral intervals or cluster-robust Krylov convergence itself.

`rootOrder` really lists the selected root first and every other root once. The descending recurrence, ordered products and actual inverse similarities are preserved. `spectralNorm` is the norm of `Matrix.toEuclideanCLM` on Euclidean space, not the default entrywise matrix norm. I inspected that actual star-algebra equivalence and its action on vectors. The finite extrema use actual real `sSup`/`sInf`; the witness endpoint/gap proofs establish nonempty bounded sets and actual attaining elements. The lower bound is compared to the genuine finite supremum over every root ordering. The zero-over-zero endpoint convention and the zero-on-invalid-samples totalization remain explicit. Invalid samples are separately proved null; they are not assumed away or used to manufacture a probability bound.

The frozen mathematical boundary, comparator, dependency pins and source provenance match their retained hashes. The sole documented configuration exception is exactly the appended Solution library registration in `lakefile.toml`; I verified the old bytes, their frozen hash and the exact appended text. Default targets remain Challenge, so the authoritative proof command is explicitly `lake build Solution`. Both canonical README and complete informal solution bytes agree with source base `32f1f799219fbcaf4c66bfaa4edb8a0c591e79e9` and preserved `deb549fa9ddd6b119e6c59016f268237e645dfa2`. This is not a claim about newer upstream main.

## Full proof path

1. `Recurrence`, `RecurrenceUnique`, `IdentityWitness`, `RegularRecurrence` and `GenericValidity` establish the literal final-state equations, descending-index uniqueness and all-ordering almost-sure validity. Convenient initialization is related to the prescribed zero initialization by a proved uniqueness theorem. At the identity sample, actual diagonal factors are products of between-block differences, each nonzero by the original admissibility assumption. This supplies valid polynomial witnesses for every fixed admissible family and every pivot; no stronger spectral-order assumption enters.
2. `PolynomialNull`, `Regular` and `RegularMatrix` prove the actual finite-product Gaussian exceptional sets are null. The polynomial argument is induction with univariate finite root sets and Fubini; variance-one Gaussian atomlessness is instantiated. Rational representations retain denominator guards, including the inversion numerator q²/denominator pq that keeps the prior guard. Matrix determinants, adjugates, inverses and trace are the genuine APIs. A deterministic witness proves a polynomial is nonzero, never that one sample has positive probability.
3. `Numerics`, `GenericWitness`, `FirstOrdering`, `LimitAlgebra` and `MatrixLimit` prove the exact nonzero limit. The rational sample gives κ=7, Q=[[30,50],[-18,-30]] and norm N=68/7; the norm proof is an actual rank-one Euclidean operator identity using `norm_rankOne`. For arbitrary good samples the actual second interpolation block is conjugated by eX−P, whose determinant is e(2e−κ). Cancellation carries explicit nonzero guards. Countably many valid epsilon samples and κ,Q₀₀ nonvanishing hold on one full-measure event, giving convergence to −Q/κ and strictly positive spectral norm. No scalar-only replacement stands in for this matrix limit.
4. `MatrixBounds`, `Endpoints` and `ExtremumBounds` derive the genuine constant lower bound. Two unit coordinate vectors and the determinant identity yield |det A|≤norm(A)², then norm(S⁻¹)^(1/2)≥8^(−1/4) for positive det S≤8. Actual similarity and recurrence prove det S₁₃=2(2−e)(2−2e), with the correct positivity and upper bound. The true cross-gap is 1, endpoints 0 and 2, and the denominator is 2e>0 throughout the full interval 0<e<1/4.
5. `Measurability`, `TotalMeasurability`, `ProbabilityBridge` and `Asymptotic` finish the original claim. Inverse and finite-extremum measurability cover singular samples too. The coupled almost-sure divergence implies convergence of the measurable sublevel indicators to the empty-set indicator under a genuine probability measure. The inspected Mathlib finite-measure dominated-convergence theorem and continuity of ENNReal.toReal at zero give the actual marginal probabilities tending to zero for every real C. A deterministic admissible family then has probability below 1/2, contradicting the full conjecture at confidence 1/2. The Nat0 sequence 1/(m+6) is the source's Nat1 sequence 1/(m+5), with no lost limiting scope.

## Execution, trust and reproducibility

I ran the fresh `reviews/referee-1-final-consumer.lean` with the pinned Lean runtime: exit 0. It uses each frozen Challenge signature with the actual Solution declaration, without importing Challenge, and independently performs all ten LeanCert kernel assertions and axiom queries. Every export closes over exactly `propext`, `Classical.choice`, `Quot.sound`. Its retained log contains only harmless unused-tactic style warnings in the consumer. The author/coordinator's completed normal build (8730 jobs), direct Solution audit and schema/coverage log were separately inspected and all receipt hashes recomputed; I did not repeat their full build or label it my execution.

LeanCert's material role here is its actual transitive kernel trust checker. I read its classification and rejection code: custom axioms, sorry axioms and compiler-trust axioms fail `kernel`. There is no claimed interval certificate in this purely exact algebraic argument. Rational matrix identities and the rank-one norm require no transcendental interval subdivision. This is the appropriate minimized computation, rather than an invented numerical backend. The independent Fraction diagnostic recomputes P,Q,κ and the squared rank-one norm identity; it is explicitly a diagnostic, not evidence replacing the Lean theorem.

`referee-1-final-check.py` verified all local-receipt source/log hashes, all frozen boundary/referee hashes, source equality at both retained bases, the exact build-only addition, the 22-file active closure and absence of active placeholders/custom axioms/native shortcuts. `referee-1-final-evidence.json` binds those files, library implementations, consumer and checker. The ten deliberate Challenge placeholders are not imported into the active proof. No mathematical source or metadata was changed during this review.

## Reuse, documentation and remaining limits

The modular finite rational-expression/null-set framework, Mathlib matrix and probability APIs, and exact 2×2 reduction are appropriate. Source credits distinguish George Stepaniants's mathematical proof, Nian Shao's framework/conjecture and Sidney Holden's AI-assisted formalization. The metadata does not claim author endorsement or human peer review. Nonblocking maintenance opportunities include using `Matrix.mul_inv_rev` instead of the short local `inverse_product` helper and cleaning deprecated/unused simplification warnings. Neither affects semantics or trust; no post-review source rewrite is requested. Frozen historical comments describing future implementation are historical context, not evidence of unfinished active proofs.

Approval is bound to the following exact active source bytes and the evidence attachment. It is a local mathematical/code approval, not an independent Linux operational report or a blanket approval of later source changes.

| Active source | SHA-256 |
|---|---|
| `NLA/KE05/Asymptotic.lean` | `15ecd3a3a3fd9180ebfc54c419f92eef8e7b489e5f08447622d276624e563be8` |
| `NLA/KE05/Definitions.lean` | `afab3cd9708f689e6261e4b88fd6b405453d48d4864f89cd03eefa323b98c538` |
| `NLA/KE05/Endpoints.lean` | `a80fe1611ef66fdd34e9abf2059f2ce6b7fa12e5e780be57db0d7ee1de4db053` |
| `NLA/KE05/ExtremumBounds.lean` | `1aa8fa8133f604ee2c31dc23362a04934160a5c24895490798d77911558f42da` |
| `NLA/KE05/FirstOrdering.lean` | `339bb8103b2fa37293002efb382fe7cc4ff1b42c883e2f243f0354bdb4566910` |
| `NLA/KE05/GenericValidity.lean` | `601f9813cfa1766ac5b41e4ddaf57072499df89381b152541b9edd8143270a65` |
| `NLA/KE05/GenericWitness.lean` | `5863a999ce26a8bc6d8a3adb436fbbb12b80ae30ad4d87056cbcda45684044e6` |
| `NLA/KE05/IdentityWitness.lean` | `56d31675bd65b17c99781309abd7832d87fa0c71d0e9ec9e88b0e7010b0e076b` |
| `NLA/KE05/LimitAlgebra.lean` | `78b73fcefa2275ec17177f8588a7eb6d396037c879ae32bb74cbf83c208a0207` |
| `NLA/KE05/MatrixBounds.lean` | `073e496c0db71b78be3a4b37089f0a93ebc8737efaffc5ddf8e64f4ec0d63297` |
| `NLA/KE05/MatrixLimit.lean` | `75596f6e2093843c5c39d9998095a7779cc3ac4c82ab8b0743935b1c5aa55be9` |
| `NLA/KE05/Measurability.lean` | `8c2b6460a36049d89aa3d0495356a39dd39217bd688dccf2e3649f40a4670ec9` |
| `NLA/KE05/Numerics.lean` | `b302e7bb9ae0430c18b06dc4ea6d0a29f61839c670d7a7d6f214a696a3803481` |
| `NLA/KE05/PolynomialNull.lean` | `b0e02c54bec09875e3f69b937de1543c5f79be563abfb07003ffaba2ca843e82` |
| `NLA/KE05/ProbabilityBridge.lean` | `6392b9197d8a9c424606c61a6d23a53a78d17c2dbabfafb735b697512b9618f9` |
| `NLA/KE05/Recurrence.lean` | `39b326ad482d64c5f64f74341253613677e99c2e642a0f22ffb07376a857a8a8` |
| `NLA/KE05/RecurrenceUnique.lean` | `03d72b222737505b12794319c24de4e071720bd2a46b1d084e014fcd66b0cb6f` |
| `NLA/KE05/Regular.lean` | `691ea94de68d81b6fc618a928bcbc8daaef36f98707549dab211322480a9f8bf` |
| `NLA/KE05/RegularMatrix.lean` | `c0841f6fbb873cd3fee039e8942d50908398ee8711c7498411128dfdf62cfc7c` |
| `NLA/KE05/RegularRecurrence.lean` | `f15e7f957cfa501df731aad9641fff02bca9166053a1977cf46157dec088f8cb` |
| `NLA/KE05/TotalMeasurability.lean` | `17cc2e066fce4d2c60eb40721accbfd1e4789bba4dee5f1096c02eced43281ec` |
| `Solution.lean` | `a7037633149823a8a451bae9ee6580d7a3bf189750cd40e68ac828c8b0e7ded2` |

`referee-1-final-evidence.json` SHA-256: `eeff902dcdc246aa8c73951e54e91ad164e9c87bc71991984a5ade013d3c3070`.

`referee-1-final-check.log` SHA-256: `ba839850df66a46508a4e540fdbd5ff885dc4868a2d8c2c17b07bd4ab385a59f`.
