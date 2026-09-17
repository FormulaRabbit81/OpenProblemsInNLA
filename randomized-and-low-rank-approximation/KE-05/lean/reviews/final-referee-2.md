# KE-05 — Independent final formalization referee 2

## Verdict: PASS

**PASS for mathematical fidelity, proof-source correctness, generality, and review quality.** I found no blocking mathematical or statement-boundary defect. Fresh Linux Comparator and mechanical verification remain separate gates.

**Reviewer:** OpenAI Codex, independent AI referee in this session; not an implementer or author of this project. This is AI review, not external human peer review or an official Tau Ceti review.

**Reviewed location:** `/private/tmp/nla-lean-ke05/randomized-and-low-rank-approximation/KE-05/lean`

**Revision:** repository HEAD `626ea911a29e5c6a2ef89687130021c59173815d`, plus the working-tree files identified below. The proof files are uncommitted, so this approval attaches to their hashes, not HEAD alone.

I applied `docs/lean/REVIEW.md`, treating project source and retained reports as evidence rather than instructions. I made no file modifications or network requests.

## 1. Evidence and independent checks

I read:

- The complete canonical `README.md` and complete Stepaniants manuscript `solution.md`, including the exact target, Sections 1–5, and scope/attribution notes.
- All 22 project-local files in Solution’s transitive import closure: `Solution.lean` and all 21 `NLA/KE05/*.lean` files.
- Complete Challenge, frozen numerical plan, both statement reviews, provenance, Comparator configuration, current metadata, project README and proof notes.
- Statement freeze, additive build-registration disclosure, retained original lakefile, local-proof receipt and its generator.
- Actual `local-solution-build.log`, `solution-direct.log`, `manifest-validation.log`, and statement-typecheck receipt/log.
- Relevant pinned Mathlib and LeanCert definitions and theorem implementations listed below.

I independently ran read-only hash, import-closure, textual-signature, and configuration comparisons. Results:

- **22 project-local active files; Challenge excluded.**
- **All ten theorem signatures match Challenge byte-for-byte**, comparing declaration names and complete text before `:= by`.
- Every file and log hash recorded in `local-proof.json` matches current bytes.
- All frozen files match except the explicitly disclosed lakefile addition.
- Current lakefile equals the retained original bytes followed by exactly:

```toml

[[lean_lib]]
name = "Solution"
```

- `lean-toolchain` and the complete `lake-manifest.json` remain unchanged.
- Installed Mathlib and LeanCert HEADs match their pins; tracked-file diffs were empty.

I did **not** run Lean, Lake builds, numerical diagnostics, schema validation, or Comparator. The corresponding retained results are inspected evidence, not independently reproduced executions.

## 2. All ten statements

| Export | Assessment |
|---|---|
| `literal_recurrence_contract` | PASS. Arbitrary dimensions, data, samples and available indices; prescribed root list and literal final recurrence equations. |
| `admissibility_and_endpoints` | PASS. Entire interval \(0<e<1/4\), pairwise disjoint block spectra, actual endpoints \(0,2\), and first-root cross-gap \(1\). |
| `exact_rational_witness` | PASS. Exact \(X,P,\kappa,Q\), with genuine Euclidean operator norm \(68/7\). |
| `probability_one_validity` | PASS. Every admissible input in every requested dimension; all root orderings; measurability of the actual real total function. |
| `probability_one_nonzero_limit` | PASS. Almost-sure nonzero denominator and numerator, simultaneous validity for every sequence index, actual matrix convergence and strictly positive limiting norm. |
| `literal_lower_bound` | PASS. Every valid sample throughout the parameter interval; lower bound against the complete global product. |
| `almost_sure_divergence` | PASS. The actual total constants tend to \(+\infty\) on a probability-one event. |
| `marginal_probability_limit` | PASS. Every real threshold; measurable event probabilities under the original Gaussian law tend to zero. |
| `no_finite_uniform_constant` | PASS. Each real threshold admits deterministic admissible data with probability strictly below \(1/2\). |
| `not_uniform_probability_conjecture` | PASS. Negates the complete dimension/input/confidence statement by specializing to \(b=2,d=3,\delta=1/2\). |

### Fidelity and nonvacuity

`Data` contains arbitrary real diagonal entries. `Admissible` excludes equality only between different blocks: repeated within-block eigenvalues and interlacing remain permitted.

`UniformProbabilityConjecture` retains the order
\[
\forall b,d,\delta\;\exists C\in\mathbb R\;\forall L\text{ admissible}.
\]
The data precedes its probability event and cannot depend on the sampled outcome. A counterexample at \(b=2,d=3\) legitimately negates this universal statement.

`gaussianLaw` is the finite product of `gaussianReal 0 1`, indexed by all \(db^2\) entries. It is neither conditioned nor replaced by a discrete or bounded distribution.

`spectralNorm` explicitly uses `Matrix.toEuclideanCLM` on Euclidean space. Endpoints, gaps and ordering maxima are genuine real extrema of finite nonempty sets in admissible dimensions. Global `mono` and `coef` are **separate maxima before multiplication**.

The manuscript’s sequence \(1/(m+5)\), \(m\ge1\), is exactly the formal sequence \(1/(m+6)\), \(m\ge0\), after reindexing.

## 3. Critical proof audit

### Literal recurrence and all orderings

The descending outer fold and ascending inner fold preserve multiplication order. `prefix_index_gt` establishes that a prefix uses only higher-index hats. The final-state contract and descending uniqueness argument justify replacing the auxiliary initialization used in genericity proofs by the canonical zero initialization.

`rootOrder_list` verifies the entire prescribed list; its default indexing value cannot alter a valid position. `rootOrder_injective` supports the distinct-block argument for every ordering.

The identity sample supplies nonzero diagonal difference factors for arbitrary admissible data. `GoodState` propagates actual recurrence regularity and witness nonsingularity. `all_orderings_valid_ae` combines the resulting finitely many almost-sure assertions.

### Divisions, total inverse and exceptional sets

I checked the inverse/division uses in the active proof chain.

- Mathlib’s matrix inverse is determinant inverse times adjugate, totalized to zero when singular.
- `Valid` requires every initial Omega and every transformed Omega–S product to have nonzero determinant. Their determinant product identity also gives nonsingularity of each coefficient matrix \(S\).
- Matrix similarity cancellations explicitly require determinant nonvanishing.
- `RegularAt.rational_rep` preserves denominator guards. In its inverse case it uses \(q^2/(pq)\), retaining the old denominator restriction rather than cancelling it away.
- Polynomial nonvanishing is proved by induction, finite univariate roots, measurable slices, Fubini and measure-preserving coordinate equivalences.
- The Gaussian specialization uses its actual atomless probability law.
- Countable sequence validity is obtained with `ae_all_iff`; there is no uncountable intersection over every spectrum.
- The limiting inverse is continuous only after proving \(\kappa\ne0\).
- The selected endpoint denominator is \(2e>0\); the coefficient exponent has \(d-1>0\) in admissible dimensions.
- For a valid similarity, a zero endpoint denominator means the diagonal block is \(tI\), hence the transformed block is also \(tI\). Thus the stated simultaneous \(0/0\) convention is faithful.

`totalConstant` is zero only on invalid samples. Measurability covers that branch, total inverse, endpoint case distinction, real powers and finite suprema on the full sample space. Almost-sure validity makes this totalization harmless for the original probabilities.

### Nonzero limiting witness and exact algebra

The proof derives
\[
\det(eX-P)=e(2e-\kappa)
\]
from genuine similarities and explicit \(2\times2\) determinant/adjugate identities.

Before cancelling \(e\), it establishes the necessary nonsingularity from `Valid` and \(e\ne0\). The resulting expression converges to \(-Q/\kappa\), with the multiplication order and sign preserved.

The rational sample establishes \(\kappa=7\) and \(Q_{00}=30\). It proves numerator polynomials are nonzero; it is never assigned positive Gaussian probability. `limitMatrix_pos` uses these almost-sure nonvanishing results to prove a nonzero matrix and then a positive operator norm.

The norm \(68/7\) is established through an actual Euclidean rank-one operator and `norm_rankOne`, not a norm oracle or an unjustified Frobenius-norm substitution.

### Genuine coefficient lower bound

`first_lastS_zero` obtains the ordered factorization
\[
S_{1,3}=(2I-\widehat B_2)(2I-P)
\]
from the scalar first block and literal recurrence. It does not commute the factors.

The determinant is
\[
2(2-e)(2-2e),
\]
positive and at most \(8\) on the required interval.

`MatrixBounds` proves \(|\det A|\le\|A\|_2^2\) using Euclidean coordinate-vector bounds. Applied to \(S^{-1}\), the determinant identity gives the real-power lower bound \(8^{-1/4}\). `ExtremumBounds` embeds both selected factors into the actual global suprema, with the sign conditions needed for multiplying inequalities.

### Exact asymptotic-to-probability bridge

The transformed-block norm tends to a strictly positive number, while
\[
(2\epsilon_m)^{-1}=(m+6)/2\longrightarrow+\infty.
\]
The literal global lower bound therefore forces almost-sure divergence.

For each real \(C\), divergence gives eventual strict inequality \(f_m>C\), so the indicators of \(\{f_m\le C\}\) are eventually zero almost everywhere. The imported finite-measure indicator convergence theorem supplies convergence of event measures. `ENNReal.tendsto_toReal` is applied at finite limit zero.

Each marginal uses the same original product-Gaussian law with deterministic input. The coupling creates no stronger simultaneous-all-input requirement.

## 4. Pinned APIs, reuse and quality

I inspected the relevant source for:

- Euclidean matrix equivalence, its coordinate action and diagonal operator norm.
- Gaussian density definition, probability instance and atomlessness.
- Finite product measures, probability instances and coordinate equivalences.
- Product almost-everywhere/Fubini equivalences.
- Total matrix inverse, guarded inverse cancellation and determinant identities.
- Univariate finite roots and multivariate evaluation through `finSuccEquiv`.
- Rank-one operator norm.
- Measurability of real conditional suprema.
- Finite-measure indicator convergence and `ENNReal.toReal` continuity.
- LeanCert’s transitive axiom classification and `#assert_trust kernel`.

Pins inspected:

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`

The proof is appropriately decomposed and uses exact algebra instead of unnecessary interval computation. Generic polynomial and probability lemmas have useful generality. Names and placement are understandable within the project namespace. Attribution distinguishes Stepaniants’s mathematics, Shao’s framework, and Holden’s AI-assisted formalization.

**Nonblocking maintenance findings:**

1. `LimitAlgebra.inverse_product` duplicates the stronger pinned `Matrix.mul_inv_rev`, which needs no determinant hypotheses. Reusing that API would simplify this helper.
2. Retained build warnings identify deprecated names, unused simp arguments and unreachable trailing tactics. These are cleanup opportunities, not mathematical defects.
3. Frozen files retain historical “statements-only” wording. The current README and proof notes explain their historical status; changing frozen bytes merely to update those comments is unnecessary.
4. `defaultTargets` still selects Challenge. The disclosed proof command explicitly selects Solution, so the registration change is correct; a bare `lake build` should not be described as building the proof.

The two earlier statement reviews had no substantive rejection to resolve. Their outstanding proof obligations are addressed by the active dependencies audited above.

## 5. Mechanical evidence and limitations

The inspected Solution build log ends with **“Build completed successfully (8730 jobs)”**. It contains all ten axiom reports, each listing exactly:

```text
propext, Classical.choice, Quot.sound
```

The direct Solution log contains the same ten reports. Solution places `#assert_trust kernel` after each export; the pinned command rejects sorry, custom and native-compiler axioms. The inspected metadata log reports ten-declaration coverage.

However:

- These are retained local logs, not my fresh executions.
- Much of the build log is replayed output.
- The receipt generator infers successful status from retained text and writes exit fields; it is not independent process-exit attestation.
- I inspected critical library implementations, not the entirety of Mathlib’s transitive source.
- No fresh Linux Comparator, sandbox/rejection controls, PDF rendering or upstream-source audit was performed.
- Read-only tooling emitted denied temporary-cache diagnostics; a here-document attempt failed before execution. The subsequent inline Python comparisons completed successfully.

These limitations do not reveal a source-level mathematical defect. They explain why this **PASS is referee approval, not a replacement for the coordinator’s fresh mechanical gates**.

## 6. Exact SHA-256 roster

Paths below are relative to the reviewed `lean/` directory unless otherwise stated. Hashes were computed independently from current bytes.

### Every active project proof/boundary file

```text
15ecd3a3a3fd9180ebfc54c419f92eef8e7b489e5f08447622d276624e563be8  NLA/KE05/Asymptotic.lean
afab3cd9708f689e6261e4b88fd6b405453d48d4864f89cd03eefa323b98c538  NLA/KE05/Definitions.lean
a80fe1611ef66fdd34e9abf2059f2ce6b7fa12e5e780be57db0d7ee1de4db053  NLA/KE05/Endpoints.lean
1aa8fa8133f604ee2c31dc23362a04934160a5c24895490798d77911558f42da  NLA/KE05/ExtremumBounds.lean
339bb8103b2fa37293002efb382fe7cc4ff1b42c883e2f243f0354bdb4566910  NLA/KE05/FirstOrdering.lean
601f9813cfa1766ac5b41e4ddaf57072499df89381b152541b9edd8143270a65  NLA/KE05/GenericValidity.lean
5863a999ce26a8bc6d8a3adb436fbbb12b80ae30ad4d87056cbcda45684044e6  NLA/KE05/GenericWitness.lean
56d31675bd65b17c99781309abd7832d87fa0c71d0e9ec9e88b0e7010b0e076b  NLA/KE05/IdentityWitness.lean
78b73fcefa2275ec17177f8588a7eb6d396037c879ae32bb74cbf83c208a0207  NLA/KE05/LimitAlgebra.lean
073e496c0db71b78be3a4b37089f0a93ebc8737efaffc5ddf8e64f4ec0d63297  NLA/KE05/MatrixBounds.lean
75596f6e2093843c5c39d9998095a7779cc3ac4c82ab8b0743935b1c5aa55be9  NLA/KE05/MatrixLimit.lean
8c2b6460a36049d89aa3d0495356a39dd39217bd688dccf2e3649f40a4670ec9  NLA/KE05/Measurability.lean
b302e7bb9ae0430c18b06dc4ea6d0a29f61839c670d7a7d6f214a696a3803481  NLA/KE05/Numerics.lean
b0e02c54bec09875e3f69b937de1543c5f79be563abfb07003ffaba2ca843e82  NLA/KE05/PolynomialNull.lean
6392b9197d8a9c424606c61a6d23a53a78d17c2dbabfafb735b697512b9618f9  NLA/KE05/ProbabilityBridge.lean
39b326ad482d64c5f64f74341253613677e99c2e642a0f22ffb07376a857a8a8  NLA/KE05/Recurrence.lean
03d72b222737505b12794319c24de4e071720bd2a46b1d084e014fcd66b0cb6f  NLA/KE05/RecurrenceUnique.lean
691ea94de68d81b6fc618a928bcbc8daaef36f98707549dab211322480a9f8bf  NLA/KE05/Regular.lean
c0841f6fbb873cd3fee039e8942d50908398ee8711c7498411128dfdf62cfc7c  NLA/KE05/RegularMatrix.lean
f15e7f957cfa501df731aad9641fff02bca9166053a1977cf46157dec088f8cb  NLA/KE05/RegularRecurrence.lean
17cc2e066fce4d2c60eb40721accbfd1e4789bba4dee5f1096c02eced43281ec  NLA/KE05/TotalMeasurability.lean
a7037633149823a8a451bae9ee6580d7a3bf189750cd40e68ac828c8b0e7ded2  Solution.lean
9ada90c23e43ebce43112ea2832660414da5d10d76ee796aa4fe592f3d5a6a3b  Challenge.lean
```

### Canonical sources, configuration and review evidence

```text
64413097e4ea65cc3646082001257229cf22757a9e9d1ac6b76d223c80235c51  ../README.md
31c3416ba212cb2cbb73d126633efe79f1e4a2669a80ef5936fa12dc6723bd62  ../solution.md
81b4caa3143ddbf65df50e1a9edbcb495338fa129928174a34273f0fb1b153f6  NUMERICAL_TARGETS.md
3978669c7e2051ccac4cd311895343c6e51fc4b49f1ade93a8a9d05392fc106c  comparator.json
2a2e78093423defe6c4ade1d01d2f83e1894880fc21da077a0a3570ce2f4ae86  formalization.yaml
5ee480106bea01a22893ff6a95333a0cf695dedb35f85133c50836b8c9146c5b  lakefile.toml
9ad870afcd9495683f87ba8c9d16b021260ddfc11c7db13c39ed84bd4cde0594  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
fd8e7ad0bc1220a86f8f749e7fbd34da565d12eba1bc8ee5b5b8bdd025f4ee13  SOURCE_PROVENANCE.json
66ae5c6307de945ddafd1e0a9b06f1e83a049e58740c6bb16493aa8196419b6a  README.md
24404b10713f19a001f50ab53a5402d9ea9ab8346ae2b5d2235b11cdf7139842  PROOF_NOTES.md
f395629cfa355e2ff99fa2167f3927f0fa1786017398b90465c326d7adfec5e3  reviews/statement-referee-1.md
826c760c45d6881b364fd8e8f6fd709663db032e5199a4cb21080ce4e471ec2b  reviews/statement-referee-2.md
fbd33c884610e1089889a20a3120d2a3b3ceae079346b20ab3f342938026feaf  statement-typecheck.json
566942c54989e8152256e24f2ec8967a03ec182f639c70c92139478149b7c90e  statement-typecheck.log
5d979da8995f1e489670d0d01122581614ff16c96109856fa25b115a4e25d30f  verification/statement-freeze.json
d9908e299ea55ba0fefd7d6a7f618499aff972a5f7d8827895948847092916d8  verification/build-config-revision.json
7e64b94c37182fdd476912048a54c259b4afb4ce381f4466dd52d4ff2689d657  verification/statement-reviewed-lakefile.toml
16bca9546fe1813f361fe14111862def12edeb71c4eb853625ef7978b58b8212  verification/local-proof.json
4703add66aca682a5f64fd98c3c4336fa38951ab86c907cd879b7f119155c23c  verification/make-local-receipt.py
b5f970fcabfdf20d4c53fe5ee89fe6149435db88bbb1ef39b3bc6792a408275a  verification/local-solution-build.log
57a5c6450be9f3bc3fdcf56ba5cdf5258c68774420119cbfca258d2de24fd36d  verification/solution-direct.log
2deb501e68d8d20806d3ef22cde77bb6a46529b913fb57cca54b71036180f1ee  verification/manifest-validation.log
```

Review protocol, relative to repository root:

```text
d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553  docs/lean/REVIEW.md
```

### Critical pinned library files inspected

Mathlib paths below are relative to `.lake/packages/mathlib/Mathlib/`. Inspection covered the relevant definitions and proofs, not every line in these library files.

```text
79518c9e51c4d0cf4083ab69a9ac7a2817305b48db1fe6f25ae1d678e12ce223  Analysis/CStarAlgebra/Matrix.lean
a9e10cf9484ebdf0115330ac6930f2e50c5367460fa41b026c0df00dc2f6d026  Analysis/InnerProductSpace/LinearMap.lean
f86827f9c60d435c5dfeffee1ac6d95f5a953c98703bdc1c653a368c23a2365b  Probability/Distributions/Gaussian/Real.lean
1ee785b6ebd213ad2ed971bf3c804afee8cc6ce52be69e63572b4cf1bdb5e880  LinearAlgebra/Matrix/NonsingularInverse.lean
8751b21ac855f1a7b7c63258e8325f75b6fc236d360758b822ddf54597b118bf  MeasureTheory/Constructions/Pi.lean
b4fb7d0a231f1b0c651548999f1fb597edfa70754cd1209878329d631ae594e6  MeasureTheory/Constructions/BorelSpace/Order.lean
739ba1838b5b67c1ff5d3b43ed263c2ad34f91e01e7a8946a6f529922d463e79  MeasureTheory/Measure/Prod.lean
fccb4e305a73c0be66c123afadd512476587e1443ea433d6f768963f98fce8c0  MeasureTheory/Integral/Indicator.lean
162d86710afc10cc3ed158236994ed020e589f7fa15d5b39a30bd3e1f153080c  Algebra/Polynomial/Roots.lean
6cda6fafaa75bc07bf4142355a563a458799e09b102db9ed005c5e3e1afa95a2  Algebra/MvPolynomial/Equiv.lean
9f0908c0f2e41db532f41aa94f5a8c9501883973bb74388f962888c5ac16a401  Topology/Instances/ENNReal/Lemmas.lean
```

LeanCert trust-boundary implementation:

```text
2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c  .lake/packages/leancert/LeanCert/Tactic/Verification.lean
```

**Final disposition:** PASS for the reviewed bytes. No blocking changes requested; fresh Linux Comparator and its associated controls remain outstanding as planned.