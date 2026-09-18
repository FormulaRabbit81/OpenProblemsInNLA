# MF-06 independent full-target source referee 2

**Verdict: PASS for the mathematical/source scope bound by MANIFEST.json.**
The complete theorem addresses the unchanged original MF-06 target. I found no
mathematical gap, weakened target, additional hypothesis on the reference
family, or substituted semantics in the reviewed proof. This is an independent
AI source review, not external human peer review, a fresh Lean run by this
referee, a Linux Comparator result, or publication/count approval.

Reviewer: `/root/mf06_final_referee2`. I did not author or modify any MF-06
statement, definition, proof, or build script. I read the complete current
119-file local `Solution.lean` import closure: 94 MF06 files, 24 unchanged
MF05/MF07 files, and Solution. I also read the canonical README and complete
informal solution, the frozen definitions and all 38 Challenge contracts, the
numerical statement sheet and correspondence, and the retained applicable
review/checker guidance. Earlier bounded reviews and the historical informal
review were not substituted for my mathematical verdict. The coordinator is a
proof author and the sole local compiler; the allocation author is not counted
as a nonauthor full proof referee.

The source boundary is local268, frozen Definitions SHA256
`9e2d95ef9d3c06fa305f7be29f428742cfa3460282abe50f3794830947f6fb39`
and Challenge SHA256
`150b8fbf15de59391b14d9aeba8d7cde59326c1b8573c277ac392d649349b1c7`.
The complete 119-source set is bound to the local268 source snapshot and record
`MF06-LOCAL-COMPLETE-268.json`, SHA256
`7c138cd627b595aa7e18c625cc39b73a673ed0434d6020664d77d769b2cdeaa6`.

## Original target and semantic checks

For every dimension d >= 1 and fixed nonempty compact family M of complex
d-by-d matrices, the final theorem chooses positive r,C before introducing the
arbitrary nonempty compact perturbation N. If its spectral Hausdorff distance
delta from M is less than r, it concludes rho(N) >= rho(M) - C delta. Neither
M nor N is assumed finite, irreducible, product bounded, nonsingular, to have
positive radius, or to preserve a given flag. This is the original target in
the retained canonical README and solution at upstream
`3923b68ecee13d02e732085a57b42a2e7e95ac7a`; I independently compared both
retained files to those Git blobs.

I unfolded the concrete definitions. `spectralNorm` is the Euclidean continuous
linear map operator norm, not the default entrywise matrix norm. Words use
`reverse.prod`; an appended letter acts on the left. `familyGrowth` ranges
over actual common-letter words, with compact finite-coordinate products
showing attainment even when the family itself is infinite. The positive-length
root infimum is proved to equal the actual growth limit, including zero radius.
The Hausdorff quantity is identified with the literal two-sided spectral
sup-inf formula, with nearest generators proved to exist. These prerequisites
are proved reused statements, not extra semantic assumptions.

The final zero-radius branch uses nonnegativity and does not invert the radius.
In the positive-radius branch, c=1/rho(M) scales both radii and Hausdorff
distance. The constants are fixed from the normalized reference, the original
neighborhood is r0/c, and division by positive c gives precisely the original
inequality. I re-read the final namespace and multiplication-orientation
repairs after the earlier source audit; they preserve the frozen theorem.

## Independent proof audit

1. **The product-bounded case (C05-C10).** The envelope is the genuine supremum
   over words, including the empty word. The finite tails are actual continuous
   seminorms and decrease to the declared infimum. Compact Dini convergence is
   used on compact sets. The maximum recurrence is proved using nested closed
   nonempty subsets of the compact generator family; it is not an unproved
   exchange of a supremum with a limit. The zero kernel is an actual invariant
   submodule. Uniform decay on its unit ball supplies one strictly contracting
   length and then exponential decay at every length. If the kernel were the
   whole space, this would contradict radius one; a zero kernel is allowed.
   A finite sum of tails produces the contracting norm on the stable component.
   The actual orthogonal projection and a coercivity argument control the
   complement. The reference cone uses a generator attaining the seminorm
   recurrence; an actual nearest generator in N gives the perturbation bound.
   The proof constructs a legal N-word for every length, so the resulting
   radius lower bound is not limited to periodic or preselected trajectories.

2. **Irreducibility and flags (C14-C16).** No Barabanov norm is postulated.
   For a nonzero vector, the span of its actual orbit is a common invariant
   subspace and hence the whole space in the irreducible case. A compact cover
   of operator/vector unit spheres gives a finite set of word bridges and one
   positive uniform lower bound. An overly large product would amplify every
   vector through bridges of uniformly bounded length. Repetition contradicts
   the already proved exponential envelope above radius one. A saturated chain
   of common invariant subspaces, extended bases, and explicit coordinate
   projections give a genuine upper block flag. The block irreducibility proof
   lifts a block invariant subspace into the corresponding adjacent flag
   interval. Similarity is implemented by an actual inverse matrix pair and
   whole-word identities, with fixed comparison factors removed at the radius.

3. **Block radius and nonresonance (C11-C13).** The upper triangular radius
   formula is proved using actual diagonal words, a common exponential envelope,
   diagonal scaling of strict upper entries, and the interspersed product
   estimate. It is not assumed as a packaged equivalence. The scalar separated
   sum proof retains zero length and uses a larger harmless constant to avoid
   square roots. For two blocks, the off-diagonal term is the exact chronological
   cut sum. Products of weights at separated cuts expose the same intervening
   original word. The tensor family pairs the two blocks of one matrix, not
   independent choices. Finite-block induction keeps the off-diagonal part of
   the grouped leading block; its tensor radius is controlled using the genuine
   block formula. Thus the strict paired-radius hypotheses imply full product
   boundedness for arbitrary compact families.

4. **Exterior, tensor and allocation semantics (C17-C29).** Exterior matrices
   are actual sorted minors, and C18 identifies them with Mathlib's exterior
   linear map in the standard exterior basis. Their identity and multiplication
   laws are proved through that map. Degree zero is a genuine one-dimensional
   identity; degrees exceeding dimension have the actual empty basis. All
   finite-dimensional norm constants are used once for a complete word rather
   than once per generator. Tensor matrices are literal reindexed Kronecker
   products. Allocations index actual products of exterior coordinate fibers.
   Coordinate extraction and assembly establish the occupation bijections and
   their dimensions rather than assuming them.

   The delicate allocation decomposition was checked separately. A nonzero
   determinant yields a nonzero permutation term. Upper triangularity forces
   row occupation weight <= column weight; equal total weights force equal
   occupation counts. The order refines weight, so different allocations of
   equal weight do not create an unproved triangular block. Grouping a minor
   can permute rows and columns separately. The proof retains those signs and
   only removes them inside determinant norms. Entrywise norm equalities alone
   are not used to infer spectral-radius equality. Instead, multiplicativity
   first identifies each block of the actual entire word and each allocation
   product; the norm comparison is then applied to that whole product. The
   same reasoning is repeated for paired blocks, retaining common letters.
   Singular and empty minors are included without dividing by determinants or
   operator norms.

5. **The critical exterior degree (C30-C33).** All exterior radii are bounded by
   rho(M)^k with the fixed norm factor outside the word length. The first
   exterior degree has the original radius, so a largest degree k with radius
   one exists. Every higher degree has radius strictly less than one. After the
   proved irreducible flag construction, every diagonal radius is <=1 and its
   family is product bounded by the irreducible/subcritical results. Allocation
   product boundedness follows. Distinct equal-degree allocations have a
   strictly larger pointwise maximum degree. Their tensor comparison combines
   the maximum allocation's strictly smaller radius with the minimum
   allocation's bounded products. C13 therefore makes the actual kth compound
   family product bounded. This conclusion is discharged before invoking the
   lower perturbation transfer; it is not an added hypothesis of the target.

6. **Perturbation transfer and C38.** The local spectral norm ball and symbolic
   determinant telescoping estimate give an actual local Hausdorff Lipschitz
   bound for the compound family. All constants depend only on M and are chosen
   before N. Applying C10 to the critical compound gives a lower bound for its
   radius; the compound radius upper bound and the elementary integer-power
   inequality transfer it to rho(N). This avoids an unnecessary numerical
   fractional-root estimate. Positive scaling and the separate zero-radius
   branch complete the full canonical statement.

## Standards, computation, and evidence

I applied the retained pinned Tau Ceti correctness, reuse, generality,
proof-quality and attribution rubrics as a source referee. I did not run the
Tau Ceti CLI. I inspected the retained Schiffer Challenge and Forsythe Challenge
and numerical-target examples, the Comparator README, and the formalization
metadata README. The independent Challenge/proof split and statement-first
freeze follow those patterns. Challenge is absent from the Solution import
closure; its 38 intentional placeholders are not imported proof assumptions.

The reuse check includes direct comparison of all 34 vendored MF05/MF07 files
with published Git commit `1b9f12661b90f40561e255293e11b2a08d79351e`.
The 24 imported ones were also source-reviewed. I searched the pinned Mathlib
Analysis/LinearAlgebra trees for joint spectral radius, Barabanov, compound
matrix and family irreducibility interfaces; the observed matches did not
provide the needed family theorem. This is a bounded API search, not an
exhaustive historical-priority assertion. The development reuses the existing
exterior map/basis, Kronecker product, block triangular determinant, finite
dimensional compactness, Dini convergence and seminorm APIs.

All matrix dimensions, word lengths, permutations, determinant sizes and
compact families remain symbolic. There is no sampled family or finite
interval grid. The only required fixed numerical certificate is the reused
half-radius certificate proved with kernel-mode LeanCert. I checked its actual
consumption, not merely the presence of its import: the local270 body dump has
three routes from C38 through the lower transfer/cone/local-ball arguments to
`NLA.MF05.half_radius_certificate`, whose body references
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`.

The coordinator ran Lean locally; I did not. I independently inspected the
local268 terminal receipt and Solution log, and replayed source/provenance
checks with the accompanying Python verifier. It matched all 119 current
source files to the immutable snapshot, re-traced all 119 selected outputs to
actual successful fresh compiler commands/logs, and checked their dependency
output hashes. Local268 freshly compiled CanonicalLower and Solution and reused
117 source-matched successful outputs; it was not a fresh rebuild of all 119.
The receipt has zero failed or blocked modules, one compiler/thread and a
4096 MiB limit. One early reused source originated under the stricter 3072 MiB
limit; its old embedded command is matched to the retained fresh receipt.
The 38 exported axiom lists contain only the configured permitted axioms.

I separately inspected the actual local270 diagnostic source and JSON dumps.
It compares elaborated types/universes in independent environments, erasing
only binder names, and all 38 agree. This diagnostic does not perform the
Comparator's independent declaration-environment checks, sandboxing or kernel
replay. The real Linux Comparator remains a separate required publication
gate. My Python replay invoked neither Lean nor Comparator. It checked 217
retained evidence hashes, 52 input hashes, all frozen headers and the actual
certificate-body edges. Its successful tool execution is retained in
REPLAY.json; this record is evidence binding, not a cryptographic guarantee
against a dishonest compiler, compromised machine, or malicious report author.

The reviewed sources credit George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, disclose substantial
Codex assistance, and preserve the original-question and reused-mathematics
attributions. No email is required or introduced by this review.

## Remaining gates and scope limit

No mathematical revision is requested. I reported the missing MF05 namespace
open during the audit; the final source fixes it without changing the frozen
header. The later positive-scaling elaboration repair is also included.

At the time of review, the project-level formalization.yaml and some prose were
the archived statement draft. They must be updated truthfully for publication;
their current mutable contents are excluded from this mathematical verdict.
Frozen historical statement comments and freeze records may retain their
historical wording. A new current-status layer should distinguish them.
The coordinator is preparing that package separately. This verdict does not
approve unreviewed workflow/metadata changes, claim a GitHub run, or increase
the completed-target count. Source changes invalidate this verdict unless
covered by an explicit source-bound continuation.
