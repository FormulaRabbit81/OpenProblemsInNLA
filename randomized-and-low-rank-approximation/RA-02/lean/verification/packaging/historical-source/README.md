# RA-02 Lean statement draft

**Not Lean verified.** This private packet proposes definitions and 27
independent proof obligations for the full negative answer to RA-02: no
absolute real constants C>0,p>=0 give a polynomial trace-error factor after
exactly r randomized Cholesky pivots on all complex PSD inputs.

Start with [the exact numerical and semantic statements](NUMERICAL_TARGETS.md),
then [definitions](NLA/RA02/Definitions.lean), [Challenge](Challenge.lean), and
[source correspondence](SourceCorrespondence.md). Definitions contain no proof
holes; every Challenge body is a deliberate placeholder. There is no active
Solution or proof implementation. Building Challenge would check elaboration,
not prove a single contract. No Lean/Lake/cache command was run locally.

The proposed finite arrowhead family establishes a sufficient 2^r/3 lower
factor. The actual process uses normalized conditional pivot masses on the
full finite path space, and the actual eigenvalue tail comes from Mathlib's
ordered Hermitian spectrum. The sole planned LeanCert certificate is exp(1)<=3;
all rank-dependent work stays symbolic. No future MF-07 proof is imported or
assumed, and no verification acceptance from another problem is borrowed.

The original mathematical resolution is by **Matthew J. Colbrook**, Department
of Applied Mathematics and Theoretical Physics, University of Cambridge.
**George Stepaniants**, Department of Computing and Mathematical Sciences,
California Institute of Technology, is the author of this AI-assisted
formalization draft and integration. The alternate finite construction is
identified as a proposed proof route; no historical novelty or stronger sharp
manuscript theorem is claimed. The original canonical page and ID stay fixed.

The finite route already has two independent mathematical preflights, retained
under `sources/reviews`. They are not approvals of this subsequently authored
statement draft. The author's earlier preflight cannot serve as an independent
statement review. Two nonauthor statement approvals, actual Linux elaboration
and immutable freeze are pending; implementation must wait. See
[the full review plan](REVIEW-PLAN.md) and [truthful metadata](formalization.yaml).

Fresh public duplicate checking covered 14 public repositories, 251 heads,
205 complete trees and 152 PR records at 2026-09-16 08:38 UTC, with no discovered
target-named RA-02/RPCholesky Lean formalization. [The bounded audit summary](DUPLICATE-AUDIT.json)
records its limits and immutable source references. Raw API responses and
contact-bearing manuscript bytes remain in the private source audit; the
packet's explicitly redacted manuscript copy preserves all mathematical text.

Schiffer and Forsythe supply inspected statement organization examples. The
pinned formalization.yaml schema, primary Comparator documentation and scoped
Tau Ceti standards are retained with provenance. These references do not
constitute external endorsement or completed checker runs. All current static
checks, source digests and the final draft inventory are separate from future
Lean execution evidence.
