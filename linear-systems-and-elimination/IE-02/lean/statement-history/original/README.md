# IE-02 statement-first formalization proposal

This is an **unrun, unreviewed Lean statement draft** for the complete original Jordan-block GMRES equality. It contains concrete definitions and 50 independent Challenge specifications. There is no Solution or proof implementation, and nothing is frozen or verified here.

For every n >= 2, nonzero complex lambda, and 1 <= k < n, the final contract states equality of the actual worst-case and ideal GMRES quantities, using the upper Jordan block, all complex normalized degree-at-most-k polynomials, and genuine Euclidean norms. It also requires an operator-minimizing polynomial, a worst-case unit vector, their common norm-attaining witness, and inner-minimum attainment for every unit vector.

Read in order:

1. `NUMERICAL_TARGETS.md` and `DEFINITION-AND-CONTRACT-PLAN.md`, written before new Lean source and sealed by `NUMERICAL-FIRST.json`.
2. `NLA/IE02/Definitions.lean`, containing actual objects and no definition holes or assumed foundations.
3. `Challenge.lean` and `STATEMENT-HEADERS.json`, the 50 proposed contracts, all intentionally unproved.
4. `SourceCorrespondence.md`, `API-SUMMARY.md`, and source/API/standard binding JSON files.
5. `REVIEW-PLAN.md` and truthful `formalization.yaml` metadata.

The finite paper route is independently accepted in the hash-bound external review packet at `/tmp/nla-lean-next-20260915/reviews/IE02-finite-route-referee-20260917`. That review does not approve these new Lean statements. Two nonauthor statement reviews, actual root-coordinated local elaboration, and an immutable root-accepted freeze are required before proof implementation. Local development remains one compiler process, one thread, 4096 MiB; final real non-root Linux Comparator/default-kernel/sandbox checks are a separate stage.

The proposed proof implements finite Schur recursion at the norm boundary and scalar weighted factorization instead of assuming them. Exact reflected coefficients preserve full complex forms; the gradient image itself is proved compact and real convex; separation gives a uniform descent including an empty complement; every extremum and Jordan transport is explicit. The optional analytic Hardy-space compression corollary is not needed by this finite route and is not exported.

One exact positive-half kernel LeanCert certificate is planned and must be consumed in the explicit descent-step positivity proof. All remaining estimates, matrix identities, and polynomial factorization are symbolic. No certificate has run.

Only this new isolated directory is owned by the statement author. No canonical page, problem number, registry, Git state, publication status, or verified-problem count was changed. Large existing source/review packets are referenced by exact paths and hashes instead of being copied again.

Mathematical authorship and formalization contribution: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. OpenAI Codex assistance. Preserve the original Tichý–Liesen–Faber problem and special cases, Faber–Liesen–Tichý approximation background, Courtney–Sarason interpolation background, and all reused Mathlib/LeanCert/Comparator code authorship and licenses. No email is included.
