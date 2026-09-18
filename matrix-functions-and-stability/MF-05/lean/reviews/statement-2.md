# MF-05 independent statement review

**APPROVE the exact 14-contract statement boundary. No mathematical correction is requested.** This is a nonauthor static mathematical/source review, not proof verification, a Lean run, a Comparator result or official Tau Ceti approval. Root must separately obtain its required local elaboration and accept the two statement reviews before freezing the proof boundary.

Reviewer: `/root/formal_review_standards`, 17 September 2026. I did not author the MF-05 definitions, statements or original mathematical manuscript. I ran no compiler, modified no candidate/source/pin/Git state, and made no canonical status or count change.

## Exact boundary and evidence

The immutable reviewed copy is `/private/tmp/nla-lean-next-20260915/MF05-statement-snapshot-20260917`. Its `STATEMENT-SNAPSHOT-MANIFEST.json` has SHA256 **`e728907ff49576fb73e778f65d5c678e323a68a7927af81dc99fc2de50a9d2f7`**. I independently checked all **86 payload files plus the outer manifest**, with exact same relative file set and bytes in the author's working draft. The author's “120 checks” refers to verifier assertions, not a claim of 120 snapshot files.

| Mathematical source | SHA256 |
| --- | --- |
| `NLA/MF05/Definitions.lean` | `f4ada429ed3cf768c228bd936c3a969f618bd3e87e8bc860cc371b5b315a3cb9` |
| `Challenge.lean` | `ebe57eb8865dc19065c2ddc0d67bc16dab6e3fa40a6b61fec0954faa7fc3dba0` |
| Original canonical README | `ba6abb75a0a1803bc9cfbfc519475d4aabb6a7454cbc8891ef04ff917b1935b4` |
| Complete original manuscript | `2a07837ba2590c157f950c166a0f667ddd0c9e3a7ee2adb71f20589b9e37e2e4` |

I read the complete [original MF-05 target](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/5308b2cfa30826e1314d6a8830415c14b5f1d7a3/matrix-functions-and-stability/MF-05/README.md) and [Colbrook manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/5308b2cfa30826e1314d6a8830415c14b5f1d7a3/references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.tex), every new definition and all 14 exact Challenge types, numerical plan, source correspondence, reuse audit, README, comparator and draft v0.4 metadata. These source objects were independently authenticated against the bound published Git commit `5308b2cfa30826e1314d6a8830415c14b5f1d7a3`. This is an immutable source review, not a fresh exhaustive search of forks or pending PRs.

I also independently authenticated all 26 published source/configuration records, including the 20 byte-for-byte MF07 modules. I read the complete reused `Definitions`, `MatrixBasics`, `CompactGrowth`, `RootSemantics`, `ProductEnvelope` and `QuantitativeComparison` modules because they determine the intended radius and the proposed reuse boundary. I did not independently rerun or reprove all 20 modules. Selected actual Mathlib operator, Hausdorff and real-power declarations were inspected and checked against pinned source commit `0df444a360eaa60ab8c11dca51a86af692955474`; excerpts and hashes are retained. Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and all ten dependency entries remain as recorded. Only the root package name changes from the old MF07 manifest.

`SNAPSHOT-BINDING.json`, `READ-ONLY-SOURCE-CHECK.json`, `STRUCTURAL-CHECK.json`, `API-EXCERPTS.md` and `CONTRACT-REVIEW.json` contain the reproducible source bindings and complete contract assessment. Preliminary `REVIEW-NOTES.md` is retained as historical reasoning written before the author seal; the final byte comparison confirms the mathematical files did not change. One ad-hoc manifest-inspection script initially tried to slice a dictionary-valued `files` field; its parser-only failure is disclosed. Corrected source binding exited 0 with an original captured log. No Lean or mathematical check failed in this review.

## Original objects and quantifiers

The final theorem fixes **any positive dimension and any nonempty compact complex family M0**, then chooses r,C>0, and only afterwards quantifies independently over both M and N. Both neighborhood hypotheses and the conclusion use the literal maximum of two sup-inf spectral distances. No finite-generator, irreducibility, normalized-radius, positive-radius, real-only or invertibility restriction is introduced. In particular it is not merely a pointwise estimate between M and the fixed M0.

The reused matrix type is genuinely complex `Matrix (Fin d) (Fin d) ℂ`; vectors are complex Euclidean space. `spectralNorm` is the norm of the actual `Matrix.toEuclideanCLM` operator. `matrixProduct w = w.reverse.prod` is the original chronological product with later matrices on the left. All words with repetition over the entire set occur. Published compact-growth results identify the supremum with an attained maximum on the full compact parameter space, not on a discretized family.

The joint radius is the actual infimum of positive-index word-growth roots. Its mandatory new `general_root_limit_semantics` proves the full original nth-root limit, nonnegativity and the family-norm bound for every eligible family, including zero radius. The positive-index infimum excludes n=0; the root sequence's harmless n=0 total value cannot affect its limit. The reused MF07 radius-one theorem alone does not establish this general statement, and the new boundary correctly does not pretend otherwise.

`canonicalHausdorff` is literally the original real sInf/sSup/max expression. The auxiliary library distance is applied to images under the actual Euclidean operator map. That map is a star-algebra equivalence, so it is injective; finite-dimensional linear continuity gives compact images, and operator distances equal spectral norms of matrix differences. Nonempty compactness gives finite distances, actual nearest generators and equality of closed sets at zero distance. These conclusions are explicit obligations. Mathlib's arbitrary zero value for real Hausdorff distance on unsuitable empty/unbounded sets cannot discharge them. The metric contract's additional d=0 case is sound: both spaces are singletons and the families are nonempty.

## Assessment of every contract

The following names have prefix `NLA.MF05.`. Exact headers, line numbers and all 14 comparator/metadata entries independently match. The comparator has no replaceable-definition exceptions and permits only `propext`, `Quot.sound` and `Classical.choice` for a future solution.

| Contract | Assessment |
| --- | --- |
| `half_radius_certificate` | True exact positive half-radius inequalities; future kernel LeanCert consumption is documented, not claimed executed. |
| `spectral_hausdorff_semantics` | Full literal/operator metric correspondence, compact images, finite edistance, symmetry, equality at zero and attained nearest generators in both directions. |
| `general_exponential_envelope` | A rate above the actual nonnegative root infimum gives a positive discount and a finite bound for every word length, including radius-zero cases. |
| `general_root_limit_semantics` | Full root convergence and radius bounds for arbitrary nonempty compact families; no normalized-only substitution. |
| `positive_scaling_semantics` | Genuine scalar images, compactness/nonemptiness, family norm, every length's growth and the radius; n=0 identity is included. |
| `exponential_bound_controls_radius` | The stated K≥1 and b>0 exponential word bound suffices for the actual radius inequality. |
| `scalar_identity_adjoin_radius` | Exact maximum formulas for the norm and radius after adjoining eI, including original radius zero; no desired formula is a premise. |
| `general_quantitative_comparison` | Exact arbitrary-radius Proposition 5 coefficient and rate, all s≥1 and all lengths including zero. |
| `controlled_comparison_norm` | The concrete discounted-word supremum is required to satisfy all four complex norm axioms, Euclidean comparisons and generator action bounds. |
| `hausdorff_radius_transfer` | Only the source family needs the chosen L-ball; the hypotheses suffice for an arbitrary nonempty compact target family. |
| `holder_scale_identity` | Correct symbolic positive real-power optimization and exact coefficient, for all positive dimensions including one. |
| `uniform_holder_estimate` | Full two-family estimate in a common positive norm ball, with positive constant and all zero/large-distance cases. |
| `local_common_norm_ball` | The genuine half-radius neighborhood lies in the explicit positive bound `familyNorm M0 + 1`. |
| `canonical_local_holder` | Exact original existential constants before both independently varying families, with literal metric and real exponent 1/d. |

## Feasibility, zero cases and absence of circularity

The planned general root bridge can use a positive block k whose root growth is below any a>rho. Submultiplicativity at n=qk+r and the finite remainder bound `max(1, max_{r<k} a_r/a^r)` yield an exponential envelope. Division is only by the positive rate, never by a possibly zero word-growth value. Infimum lower bounds and roots of the envelope then give full convergence, including zero growth. This is a genuine new proof obligation.

Adjoining eI preserves the order of all remaining factors in each word; its scalar factors commute, so no spurious binomial-count penalty is needed. Old words and all-identity words give lower bounds, and an envelope above max(rho,e) gives the upper radius bound. Positive-radius families can then be normalized for the published comparison. At radius zero, adjoin eI with 0<e≤L, apply the positive-radius result and let e decrease to zero in the scalar fixed-length bound. This argument uses scalar continuity, not the desired continuity of the joint spectral radius. Thus the difficult normalized MF07 theorem can be reused without circularity or new radius assumptions.

Under d≥1,L>0,s≥1, the comparison factor `d*s^(d−1)` is at least one and the comparison rate is positive. The exact-rate discounted envelope is finite because the proposed quantitative comparison bounds every length at that rate; the existing `ProductEnvelope` lemmas then provide genuine norm axioms. There is no assumed extremal norm or encoded spectral-radius oracle.

For the one-sided transfer, choose A in M close to B in N. The proved norm bounds give `p(Bx) ≤ (u + κ δ)p(x)`. Iterating all N-words gives an actual Euclidean exponential bound, which the radius-transfer contract converts to the desired inequality. This explains why no separately supplied L-bound on N is needed there.

When 0<δ≤L, the symbolic choice `s=(L/δ)^(1/d)` gives `s^d=L/δ`, `κδ=dL/s` and the exact coefficient `d(2d+1)L^(1−1/d)δ^(1/d)`. Every real-power identity uses positive bases. Zero distance gives identical compact families; δ≥L uses both radii in [0,L]. Dimension one is retained with the source's valid nonoptimal constant 3; the sharper scalar constant 1 and sharpness examples are outside the original existential target. For local constants, nearest points in M0 and the norm triangle put both nearby families in `familyNorm M0+1`, with the common certified radius 1/2. No finite computation substitutes for these universal arguments.

## Review standards, attribution and remaining gates

I applied the retained Tau Ceti correctness and generality guidance by checking every definition, explicit quantifier, total-choice/supremum behavior, zero case and potential moved assumption. The retained standard bindings record Tau Ceti revision `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`; this is scoped use of those texts, not an official service review. The natural specialization is the exact complex compact-family problem. Supporting positive-scalar and metric results have appropriate hypotheses; no speculative noncompact extension is necessary. Proof quality and transitive kernel trust remain for the actual implementation review.

Reuse and attribution are explicit: Colbrook's original mathematical argument and the published MF07 formalization are named in code and documentation, with exact namespace/source preservation. The canonical page retains Epperlein–Wirth's original conjecture reference. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. No George email is added. Schiffer/Forsythe are workflow examples, not silently imported theorems.

The draft metadata is truthful about 14 intentional Challenge placeholders and zero new MF05 implementations; its proof-development sorry count is explicitly scoped to those nonexistent implementations. It makes no measured-axiom, completed-target, independent-review or execution claim. The planned sole new exact certificate is `0<1/2<1`; no extra numerical box is needed, and its actual material kernel consumption must be established later.

**Required fixes: none.** This approval is only for the exact mathematical statement boundary. It does not authorize starting proofs without the coordinator's gate, does not certify the future implementation or inherited proof closure, and does not increment a completed-target count. Root-controlled local elaboration, two accepted statement reviews and freeze, complete local proofs with independent final reviews, and the actual non-root GitHub Comparator/kernel/sandbox checks remain distinct requirements.
