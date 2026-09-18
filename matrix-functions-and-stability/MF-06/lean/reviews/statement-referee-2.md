# Independent MF-06 statement review

**Verdict: APPROVE the statement boundary, and only that boundary.** Reviewer:
`/root/mf06_statement_referee2`; statement author: `/root/ie02_full_referee2`.
The reviewer did not author these definitions or contracts, did not implement
proofs, and did not modify the draft, Git worktrees, or compiler caches.

The approved draft manifest is
`f37bf9237fb7a3dbff8d917597d39d549e69ce14640f326e7b38b254dbd40c21`.
Its 81 payloads were independently hashed and copied into this packet.
The two active Lean sources are Definitions
`9e2d95ef9d3c06fa305f7be29f428742cfa3460282abe50f3794830947f6fb39`
and Challenge
`150b8fbf15de59391b14d9aeba8d7cde59326c1b8573c277ac392d649349b1c7`.
The numerical sheet, read before the Lean sources, has hash
`304f40499a15132b4ddb0b73e5d9b401e6cd0bf05826349ece377685d32574c1`.

This is one independent statement approval. It is not a second approval, a
statement freeze, proof completion, an independent compiler rerun, a Comparator
run, a Tau Ceti service verdict, or a historical-priority certification. It
does not increase any completed-target count. Root must combine the required
independent approvals with the actual local elaboration evidence before freezing
statements or starting proof bodies.

## Mathematical scope and attempted counterexamples

I read the complete numerical sheet, every one of the 37 new definitions and
abbreviations, all 38 Challenge contracts, the entire canonical README and
solution, and the source correspondence. The final contract C38 says: for every
positive dimension and fixed nonempty compact complex matrix family, there are
positive constants chosen before the unrestricted nearby nonempty compact
family, such that its radius has the required linear lower bound. No finiteness,
irreducibility, invertibility, product boundedness, shared invariant subspace,
or positive reference-radius assumption was added to C38.

The radius and Hausdorff distance are the unchanged concrete MF07/MF05
definitions. The former uses all chronological words and an infimum of their
root growth; C03 gives the actual arbitrary-radius limit. The latter is the
literal maximum of two supremum-infimum formulas in the complex Euclidean
operator norm; C02 connects it to the metric formulation and attained nearest
generators. Compactness and nonemptiness are present where real suprema and
infima require bounds and witnesses. The totalized real supremum of an
unbounded set is not used to simulate a product bound in these contracts.

I tested the statement meanings against the following mathematical edge cases:

- A singleton zero matrix has zero reference radius. C38 retains this case;
  normalization is only used for positive radii. No nearby positive-radius
  hypothesis occurs.
- The singleton Jordan matrix with both diagonal entries equal to one has
  radius one and unbounded powers. C33 must handle it; its second compound is
  the scalar identity. C38 does not replace this case by C10's product-bounded
  reference hypothesis.
- For the diagonal reference matrix with entries one-half and one, the stable
  gauge is the absolute value of the second coordinate. Its kernel is a
  nonzero proper stable subspace. C08 permits this case as well as the bottom
  subspace; C10 permits perturbations with a nonzero lower-left block.
- A compact infinite family of unitary matrices is still within scope. The
  word sets are not lists of finitely many generators, and the final perturbed
  family need not be finite either.
- Two identity diagonal blocks with a nonzero upper-right block show why C13's
  strict paired-radius hypothesis matters: the paired radius is one, so that
  genuinely unbounded Jordan example does not satisfy the hypothesis.
- Degree zero gives a one-dimensional scalar identity, including at a zero
  matrix; degrees above the ambient dimension have an empty exterior basis.
  The positivity and radius contracts impose `k ≤ d` where necessary. Empty
  words, zero factors, singular minors, zero Hausdorff distance, a zero-length
  scalar sum, and empty block fibers in contracts allowing them are preserved.

None exposed a false contract, vacuous replacement of the target, or a hidden
assumption supplying one of the required foundations.

## Definitions

`IsProductBounded` bounds the actual family growth at every natural length,
including zero. `FamilyInvariant` uses the original matrix action on complex
submodules; `FamilyIrreducible` permits exactly bottom and top invariant
submodules. Their nontrivial consumers and constructive conclusions occur in
C08, C13–C16, and C33. These predicates do not contain the perturbation theorem.

`boundedEnvelope`, `tailValues`, `tailEnvelope`, and `stableGauge` are actual
word suprema and a decreasing-tail infimum. Their norm, seminorm, continuity,
recurrence, and proper-kernel properties are conclusions C05–C08, not fields
assumed in a replacement structure. `restrictedGrowth` inserts zero before
taking the supremum over actual unit vectors in the proposed submodule, so the
bottom submodule has a defined zero bound. The cone constants are precisely
the real rational expressions inspected in the numerical sheet.

`conjugateFamily` is the literal image under `R*A*Q`; every contract using it
for a change of basis supplies both inverse identities. Block labels partition
the original coordinates into literal fibers. `blockDim`, `blockCoordinate`,
`blockMatrix`, and `diagonalFamily` use those fibers and their finite-coordinate
equivalences. Upper triangularity vanishes in the correct direction. The
surjectivity assumptions in the radius and flag contracts ensure positive block
dimensions. The labels need not be contiguous; fixed regrouping of coordinates
is a legitimate change of basis, which later proof bodies must establish.

`ExteriorIndex`, `compoundDim`, `compoundIndex`, and `minorCoordinate` use
actual sorted subsets and order embeddings. `compoundMatrix` consists of
the corresponding minors, and its family is an actual image. C18's coordinate
formula matches Mathlib: applying `basis_repr_apply`, `map_apply_ιMulti_family`,
and the standard-basis coordinates gives the transpose of the specified minor;
determinant invariance under transpose gives exactly the stated orientation.
This is not an arbitrary function with assumed exterior properties.

`tensorMatrix` is the genuine Kronecker matrix reindexed by `finProdFinEquiv`.
`pairedFamily` uses the same original generator in both factors. Allocation
degrees lie between zero and their actual block dimensions. The finite product
coordinate space retains zero-degree factors; `allocationMatrix` is the literal
product of actual compound-block entries, all from one original matrix. Its
family does not allow independent choices of a generator in different factors.
Pointwise maximum and minimum allocations stay within the allowed degrees.

## All contract decisions

Every row below is approved as a statement obligation or exact reuse boundary;
it is not a proof-verification claim.

| Contract | Adversarial mathematical check |
|---|---|
| C01 | Exact existing kernel-mode half-radius certificate; meaningful consumption remains a future proof requirement. |
| C02 | Exact existing compact Hausdorff correspondence, with both directions and zero-distance equality. |
| C03 | Exact existing nonnegative arbitrary-radius root limit, including radius zero. |
| C04 | Exact existing positive scaling, including every word length; no division by zero. |
| C05 | The empty word supplies definiteness and the product bound supplies finiteness; all generators contract the concrete envelope. |
| C06 | Uniform envelope Lipschitz control gives a continuous limiting seminorm; monotonicity plus compactness supplies compact-uniform convergence. This is a conclusion, not a premise. |
| C07 | Compact attainment and uniform convergence on the orbit of a fixed vector justify a true maximum recurrence, not only a supremum. |
| C08 | Uniform decay on the unit sphere of the kernel yields a finite-length contraction and hence exponential decay. A top kernel contradicts radius one. Bottom is allowed. |
| C09 | The cone inequality reduces to `L^2*t ≤ 1`; `L ≥ 2` gives the half lower factor, including the equality endpoint. |
| C10 | Exactly the product-bounded-reference lemma; its robust quotient/cone construction remains to be implemented for arbitrary perturbations. |
| C11 | The cross-cut argument bounds `X*(X-2*K)` by `4*G`; the larger displayed constant is valid without a square-root computation. Length zero is immediate. |
| C12 | The actual finite triangular block maximum formula is correct, including zero diagonal radii. Common original words are preserved. |
| C13 | Pairwise tensor gaps and bounded diagonal words suffice by the two-block separated-sum estimate and grouped-prefix induction. No off-diagonal term is silently omitted. |
| C14 | Irreducible compact radius-one families are product bounded; the substantive extremal-norm consequence must be proved, not imported as a new axiom. |
| C15 | A finite composition flag exists for an arbitrary family acting on a finite-dimensional complex space. Compactness or nonemptiness is not necessary for this algebraic statement. |
| C16 | A fixed actual similarity changes word norms by bounded constants and preserves the radius and product boundedness. |
| C17 | Exterior dimension is the binomial coefficient; the positivity range includes degree zero and excludes above-dimensional degrees. |
| C18 | The exact sorted-minor/exterior-map coordinate identity has the correct orientation after determinant transpose. |
| C19 | Exterior multiplicativity and identity work for singular matrices, degree zero, and empty exterior bases. |
| C20 | Each determinant has at most `k!` terms; the output matrix norm is at most its dimension times its maximum entry. The dimension-only constant is outside the word-length exponent. |
| C21 | Telescoping a product of `k` entries gives the stated `N*k*k!*L^(k-1)` bound. Positive `L` and positive degree give the asserted positive constant. |
| C22 | The Kronecker multiplication identity preserves pairing and chronological multiplication, including empty coordinate types. |
| C23 | Entrywise upper bounds give both conservative norm comparisons; no zero factor is divided out. Positive factor dimensions are explicit. |
| C24 | Fibers partition all coordinates; the permitted degrees sum to at most `d`, and each compound index is nonempty. The empty product of factors has dimension one. |
| C25 | Actual upper triangularity ensures a product's diagonal blocks are the products of the matching diagonal blocks. Both matrix hypotheses are present. |
| C26 | Triangularity is correctly unnecessary here: the allocation product factors into products of the diagonal-block generators from the common word, whether or not those equal diagonal blocks of the full product. |
| C27 | The exterior decomposition is triangular by cumulative block occupation. Arbitrary fiber enumerations can require fixed signs/permutations; proving that identification is part of the obligation. |
| C28 | Distinct equal-total-degree allocations have a strictly larger max total and strictly smaller min total. Tied coordinates do not invalidate strictness. |
| C29 | For any matrix `P`, tensor-factor norms can be regrouped into max/min allocations. A finite uniform constant suffices; the assertion remains true with zero factors. No triangularity is needed for this pointwise identity. |
| C30 | The max allocation has strictly higher permitted degree, hence exponential decay; the min allocation is product bounded. Their common-word tensor bound gives a strictly subunit paired radius. |
| C31 | Full allocation nonresonance controls the complete triangular exterior matrix family; it does not assume its desired product bound. |
| C32 | Polynomial images are nonempty compact. Multiplicativity and the fixed dimensional factor give exact radius-power domination; degree one is a fixed coordinate permutation of the original matrix. |
| C33 | Degree one ensures a critical degree exists, while the dimension bounds it. The maximal such degree has all higher gaps and is product bounded by the preceding full block/exterior route. Unbounded normalized original products are retained. |
| C34 | Matrix local Lipschitz bounds apply to both nearest-generator directions in the actual Hausdorff formula; injectivity of the compound map is unnecessary. |
| C35 | Positive scaling multiplies each distance, infimum, and supremum by the same positive scalar. |
| C36 | For `u ≤ 1`, its positive integer power is at most `u`; for `u ≥ 1`, `z ≤ 1` suffices. No fractional-root computation or positivity of `u` is hidden. |
| C37 | The critical compound reduces the arbitrary normalized reference to C10. Nearby families are unrestricted and need not share a flag. |
| C38 | The final unchanged target follows after positive normalization; radius zero is a separate nonnegativity case. Constants precede the quantified perturbed family. |

## Reuse, numerical work, and standards

The applied Tau Ceti rubrics are correctness, generality, reuse, attribution,
and proof quality at the pinned `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`
snapshot. This was an agent review using those documents, not execution of
the Tau Ceti CLI or its isolated review service. Correctness and target
generality are approved. No statement revision is required. The material is
at the concrete level needed by this canonical project; this is not a claim
that every specialized contract would be the preferred public Mathlib API.
Proof-body quality remains unreviewed because no new implementation exists.

I independently matched the canonical README, solution Markdown, and solution
TeX against Git objects at upstream `3923b68ecee13d02e732085a57b42a2e7e95ac7a`.
Eleven reused MF05/MF07 files match published commit
`06b8cf49740205c4b7b0b71ee5c636855fbe26a6`. The four C01–C04 headers match their
actual implementation sources exactly; no new forwarding wrappers were added.
Eleven referenced Mathlib files match Git objects at pinned commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

The inspected API declarations cover the real `Seminorm`, finite equivalences,
sorted subset indices, standard and exterior bases, `exteriorPower.map`, matrix
linearization, genuine Kronecker multiplication, and antitone Dini convergence.
Fresh searches over the pinned Mathlib tree found no joint-family radius,
Barabanov, or critical-compound replacement for the new substantive obligations;
the broad textual query's few spectral-radius hits concern selfadjoint single
operators, not these statements. This is a bounded local reuse search, not a
claim about all possible formalizations or remote repositories. Full proof
review must repeat targeted reuse checks for substantial new proof bodies.

The original question's scope was also checked against Epperlein–Wirth,
[Conjecture 3(P2) and Section 3](https://arxiv.org/html/2311.18633v2).
The paper's pointwise exponent-one target has the same fixed-reference order;
its irreducible-family background supports the mathematical prerequisite C14,
without supplying a Lean proof of it.

The numerical plan uses the already published kernel-mode LeanCert half-radius
certificate. Its actual source was read. Its consumption in the future cone
and transfer proofs must still be checked; an unused import will not suffice.
All other numerical bounds remain symbolic. Larger internal constants avoid
unnecessary exact Hilbert-tensor identities, square roots, interval subdivisions,
word enumeration, and permutation enumeration without weakening the target.
The Schiffer/Forsythe provenance in the draft is about statement-first and
independent-Challenge structure; neither is claimed as a mathematical premise.

George Stepaniants's name and Department of Computing and Mathematical Sciences,
California Institute of Technology affiliation are present without his email.
The canonical solution attribution, Epperlein–Wirth target, Barabanov/Wirth
background, Chitour–Mason–Sigalotti and Morris context, and Matthew J. Colbrook's
reused mathematics remain identified. No authorship transfer is inferred from
formal reuse.

## Actual execution evidence and remaining gates

I read and independently source-bound root's completed local run177 receipt
and both logs. Four old modules reused matching successful outputs; the new
Definitions elaborated in 26.46 seconds with an empty log, and Challenge
elaborated in 24.30 seconds with exactly 38 intentional placeholder warnings.
The recorded commands use one thread and a 4096 MiB limit. This is actual
root-run statement elaboration, not proof acceptance and not an independent
rerun by this reviewer. I invoked no Lean, Lake, or Comparator process.

The draft metadata says uncompiled/unreviewed because it records its author-side
handoff stage. This review and run177 are later separate evidence. Before freeze
or publication, the coordinator should create a current stage record while
retaining that history. The draft still correctly has no completed main result,
no Solution, no proof implementation, and no Comparator success.

The new statements leave substantial work: stable-kernel uniform decay and
quotient/cone trajectories; irreducible product boundedness and invariant flags;
full finite-block nonresonance; and actual exterior triangularization and
critical-compound product boundedness. None may be changed into a hypothesis
or dropped after this approval. Both final nonauthor proof reviews, complete
local proof checks, truthful final metadata, and actual Linux Comparator/kernel/
sandbox/negative-control runs remain required before MF-06 can count as Lean
verified or be submitted as a completed formalization.

`verify_review.py` is a read-only integrity and evidence-consistency checker.
It verifies the sealed snapshots and the scope described above; it does not
verify the mathematical reasoning or replay Lean. Mathematical approval is the
independent analysis recorded in this report, not the number of file checks.
