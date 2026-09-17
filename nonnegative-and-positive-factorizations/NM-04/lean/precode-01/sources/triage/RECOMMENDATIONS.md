# Next-target triage after local123

Recommend **MF-05 first, NM-04 second**, on separate statement-first tracks. This is a feasibility packet, not a proof, statement freeze, completed formalization, new verification count, or new public duplicate audit.

The exact upstream source is `849003686970b372e1b2128ba072f86168f81d38`. Its append-only registry has 217 canonical entries: 47 marked Lean verified, 57 Solved, 71 Partially resolved, and 42 Open. The retained campaign snapshot records 50 accepted distinct targets: 31 baseline, 14 accepted submissions, and 5 accepted overlapping submissions. Three accepted submissions (MI-13, RA-02, SF-01) are still marked Solved at this upstream object. Excluding those and the active final packages IE-02/SP-15 leaves **52 eligible solved targets**. The stale campaign `remaining` array was not used.

`INVENTORY.json` binds every canonical README to its Git blob and SHA-256, and records each exclusion. Retrieval of all 217 pages is not a claim that all 217 mathematical arguments were read. The semantic shortlist and read scope are in `SHORTLIST.md`. This refresh does not re-audit the 50 historical acceptances; it uses the parent-requested acceptance record. No count has been advanced.

## 1. MF-05: full local two-family Hölder continuity

The target quantifies over every dimension and every nonempty compact complex matrix family, with two independently varying nearby families, the actual spectral norm, and its Hausdorff metric. Zero joint spectral radius, reducibility, and infinitely many generators remain included.

The completed MF-07 formalization supplies concrete definitions of words, spectral norm, word-growth maxima, and joint spectral radius as an infimum of positive-index roots, together with compactness/attainment, submultiplicativity, product-envelope norms, Auerbach coordinates, unitary geometry, and the difficult rounded-norm comparison argument. The exact upstream 20 active modules plus Challenge, Solution and three configuration files are retained under `reuse/upstream/`. Nine retained preparation files differ from upstream, including seven proof files; `reuse/MF07-preparation-vs-upstream.diff` was read. Reuse must select the exact published bytes, not the stale preparation files. The quantitative comparison, root semantics, product envelope and concrete definitions inspected for this plan are source-matched to upstream.

**Important boundary:** the public `NLA.MF07.quantitative_comparison`, approximate-extremal-norm theorem, and root-limit equivalence assume radius one. They do not already prove MF-05 or the arbitrary-radius growth estimate. The plan supplies the missing general root semantics and generalization, including radius zero, without postulating continuity of the joint spectral radius.

The preferred route is positive scaling plus adjoining a small scalar identity. It reuses the published quantitative comparison intact. General finite-block exponential envelopes prove the radius of the enlarged family is `max(radius, epsilon)`. Normalization then handles positive radius; letting epsilon decrease to zero handles radius zero. A discounted-word norm transfers the perturbation estimate, and an algebraic choice of a positive d-th root optimizes the coefficient. This avoids repeating the Auerbach/SVD/triangular-damping proofs.

The final local constants may be `r = 1/2`, `L = familyNorm(M0) + 1`, and `C = d(2d+1)L^(1-1/d)`. A single kernel LeanCert certificate for the half-radius is genuinely consumed when proving the common norm-ball inclusion and `r > 0`. All dimensions, products, limits and real powers remain symbolic. No interval subdivision or large finite matrix calculation is needed.

**Bounded new work:** scalar-image growth and radius; finite-block exponential envelope and full root-limit semantics; scalar-identity adjunction; spectral Hausdorff wrapper; norm transfer and real-power optimization. No new deep spectral theorem was identified as a prerequisite. Definitions and every quantifier are specified in `NUMERICAL-OBLIGATIONS.md` before any new Lean code.

## 2. NM-04: full Rowland–Wu identity

The target covers every positive real rectangular matrix, all positive dimensions, all displayed coefficients and four signed adjacency cases, including vanishing minors and one-row/one-column cases. Proving only an algebraic-degree bound, a square-matrix case, a sampled null vector, or a relation conditional on an unexplained Sinkhorn oracle does not meet it.

The complete retained manuscript gives a finite algebraic route: express the coefficient sum as one determinant, establish four universal cofactor/minor identities, construct an explicit nonzero null vector after balancing, and transport it through positive diagonal scaling. The final determinant is never expanded into permutations or all numerical subsets. Universal multilinearity, alternation and principal-minor identities do the work.

The search found no ready Sinkhorn/matrix-scaling existence theorem. The exact canonical statement explicitly defines the limit equivalently as the unique positive diagonal scaling with the prescribed margins. The plan therefore proves that existence and uniqueness directly. A coercive log-sum-exp functional on the mean-zero hyperplane has a minimizer; its derivatives give the required column margins after row normalization. A maximum argument proves uniqueness of the balanced matrix. This uses finite-dimensional compactness, logarithm/exponential calculus and finite sums; it does not require a fixed-point theorem, an iterative convergence theorem, or an external scaling assumption.

**Bounded new work:** sorted equal-cardinality minor indices and their signs; the general rank-one determinant/cofactor formula valid for singular minors; four minor identities; weighted principal-minor expansion; positive rectangular scaling. The pinned Schur-complement file explicitly leaves the singular rank-one formula as a TODO, while its existing determinant lemma assumes an invertible matrix. That missing generality must be proved from multilinearity; the nonzero-minor assumption cannot be added.

This second track is larger and has more combinatorial bookkeeping than MF-05. It is still preferable to candidates needing a new theory of semialgebraic complexity, graph positive-semidefinite rigidity, operator-monotone representation, or projective border rank. No estimate of a guaranteed completion date is made.

Seven small exact rational diagnostics checked the actual four-case H definition and null vector, including rectangular matrices, both degenerate dimensions, and vanishing minors. They all pass, with at most six minor indices. Their code, inputs and outputs are retained. They are source-convention diagnostics only, not universal proof certificates and not Lean runs.

## Gates and attribution

Neither recommended target has a target-named `.lean` or `formalization.yaml` at the exact upstream object; neither appears in the retained five `next-proofs` directories. This is a local object check only. The parent will refresh public forks/branches/PRs before statement preparation. Existing permanent IDs, original questions and canonical paths must be preserved.

Next steps are exact definitions/Challenge drafting, two independent nonauthor statement reviews, root-controlled actual local elaboration and freeze, then implementation. Final full source reviews should apply all five pinned Tau Ceti rubric scopes without claiming endorsement by that service. Comparator contracts must compare the full targets and actual definitions. `formalization.yaml` must distinguish preparation, local Lean evidence, Linux Comparator evidence and publication. One PR per completed target goes to `ajt60gaibb/OpenProblemsInNLA:main` after the existing final gates.

No Lean, Lake, compiler, cache, Git mutation, network request or candidate mutation was performed during this triage. Only this private packet was written. Future compilation remains one root-controlled local process, one thread, 4096 MiB; source agents can work in parallel. Final Comparator/kernel/sandbox checks remain actual non-root Linux GitHub runs after local success.

Preserve Matthew J. Colbrook's mathematical authorship and all reused code authorship. Credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, for his formalization contribution; do not publish his email. The retained original manuscript bytes are private provenance copies and include the original author's contact preamble. The new public package can reference those originals by URL and hash without republishing contacts; preserve the author name, affiliation and original hash. This packet does not publish those files.
