# IV-03 final mathematical and source review — PASS

Reviewer: `/root/iv06_statement_referee_1`, an independent AI agent. I authored neither the IV-03 statement draft nor any IV-03 proof module. This review applies the repository's Tau Ceti adaptation in `docs/lean/REVIEW.md`; it is not human peer review or an official Tau Ceti review.

**Verdict: PASS for the complete mathematical scope, proof source, and local exported-type/trust checks.** I found no blocking correction. The isolated Linux Comparator and its operational controls remain separate pending gates.

## Exact reviewed boundary and provenance

I read the complete canonical README and the complete Colbrook IV-03 manuscript, all 1,145 lines of the twelve active `NLA/IV03` modules, the entire `Solution.lean`, frozen Challenge and definitions, numerical plan, project metadata, proof notes, and actual local build/export logs. Every active source and each inspected library file is SHA-256 bound in `referee-1-final-evidence.json`; `referee-1-final-check.py` reproduces the source, boundary, and receipt checks.

The original canonical README has SHA-256 `c5c92b828ae968b01e53dab0e71b9adca662efe0075f8928606dc5e671c439d2`; the complete manuscript has SHA-256 `f09cb222b822704855031d18c971b3d61dbea4a371ee4547414c9e40500c3e98`. I independently compared their bytes with both preserved source commit `deb549fa9ddd6b119e6c59016f268237e645dfa2` and actual base `32f1f799219fbcaf4c66bfaa4edb8a0c591e79e9`. All seven frozen statement/configuration hashes still match `statement-freeze.json`. The reviewed proof is the working-tree candidate bound by hashes; the current checkout HEAD alone is not a claim that uncommitted proof bytes belong to that commit.

## Fidelity, correctness, and full scope

The boundary retains every real dimension n≥1, arbitrary entrywise ordered endpoints, independently varying entries, both closed endpoints, zero widths, zero entries, and reducible matrices. `IsInverseM` uses actual matrix `IsUnit`, entrywise nonnegativity, and the actual inverse's off-diagonal signs. I checked Mathlib's total inverse and `isUnit_iff_isUnit_det`: the explicit unit guard prevents singular matrices from passing because their totalized inverse is zero. No interval regularity or positive-entry hypothesis has been introduced.

All four exports match the frozen types. `vertex_formula` connects the pointwise vertices to the actual two-sided diagonal matrix product. `vertices_admissible` handles both signs. The n² negative-sign equivalence quantifies every interval member; the final theorem derives the complete original 2n² equivalence from that stronger result. Repeated vertices, including dimension one and zero-width intervals, are harmless. The source's complexity discussion is explicitly excluded from the formalized claim.

The proof chain is substantive and closed:

- `Proof` derives the Z-matrix maximum principle, actual invertibility and inverse nonnegativity from a positive weight. Its determinant homotopy proves positivity without a determinant-sign assumption. Removing nonpositive off-diagonal contributions supplies principal weights.
- `Principal` derives every block invertibility before applying Mathlib's actual block inverse identities. It handles arbitrary finite embeddings through a genuine complement equivalence, including the empty principal block. Both transfer-sign lemmas derive their signs from inverse block equations.
- `Complementary` proves the required principal-minor identity from block determinant/inverse formulas. `Adjugate` excludes determinant zero through the actual rank inequality for a zero matrix product and a nonzero codimension-one minor; its exact three-index argument excludes a negative determinant. This is where interior regularity is established, not assumed.
- `Cofactor` uses the actual `adjugate_apply` row-replacement determinant and a two-by-two Schur calculation. Its only inverse premise concerns the complementary block; it does not invert the possibly singular full matrix. I checked the row/column orientation and the minus sign against the actual Mathlib definition.
- `Monotonicity` proves an exact resolvent/bilinear identity. `SchurInterval` obtains every needed transfer sign from explicit row/column endpoint replacements that remain inside the original interval. This replaces the manuscript's derivative argument while retaining the full box. `IntervalStructure` proves principal compatibility of vertices, and the strong induction supplies every proper-block hypothesis used in the comparison.
- `Vertices` checks dimensions one and two explicitly; `IntervalAdjugate` and `IntervalInduction` handle all higher dimensions and conclude genuine inverse-M membership. No core source lemma has been retained as an unproved assumption.

## LeanCert, computation, reuse, and attribution

This proof is symbolic. It uses exact finite sum/order algebra, true matrix inverse/cofactor/rank APIs, and determinant continuity; no sampled grid, interval subdivision, floating-point calculation, or numerical certificate is needed. The algebraic Schur and cofactor replacements reduce proof work without reducing scope.

LeanCert is used for actual `#assert_trust kernel` audits, not represented as a numerical interval backend here. I inspected its trust command: it collects transitive axioms and rejects `sorryAx`, custom axioms, and native-compiler trust in kernel mode. I also inspected the material Mathlib inverse, Schur, rank, and adjugate APIs. Source authorship remains Matthew J. Colbrook, with Sidney Holden's formalization credit and explicit AI assistance. No source-author endorsement, external human review, or official Tau Ceti endorsement is claimed.

## Actual execution evidence and limits

My fresh `reviews/referee-1-final-consumer.lean` reuses all four frozen types verbatim as examples, consumes the corresponding actual exports, runs four LeanCert kernel trust checks, and prints all four transitive axiom closures. The pinned Lean 4.33.1 command exited 0; each closure is exactly `[propext, Classical.choice, Quot.sound]`. Its complete output is retained in `referee-1-final-consumer.log`.

I inspected, but did not execute, the author's complete `lake build Solution` log: PASS, 8,804 jobs. The source/log hashes match its local receipt. Existing style warnings concern `letI`, unused simplification arguments, and tactic sequencing; the log contains no proof error or placeholder warning. My separate reproducible hash/source check also exited 0. The imported foundation files were source-reviewed and are covered by the author's full build; my independent consumer is not described as a second full dependency rebuild.

No Linux Comparator, sandbox-isolation, rejection-control, publication, or canonical Lean-verification status is approved by this report alone. Those gates remain required. No source or metadata was modified by this review.
