# MF-07: scoped review of the root-authored repair for run 35094433103

**Verdict: approve this exact narrow source repair for a coordinated Linux rerun.** This is not runtime acceptance, a completed MF-07 formalization, or a count change.

## Reviewer role

The executor is `/root/mf22_publication_referee`. I did not implement this repair; the root agent did. I authored earlier MF-07 proof modules, so this report is a nonauthor review of the present patch only and **does not count as an independent final mathematical review of the entire MF-07 proof**. Final whole-source independent reviews and successful actual execution remain required.

## Exact scope and findings

I read the complete changed `SingularCoordinates.lean`, its before/after patch, the complete actual MF-07 diagnostic log, all frozen public contracts, the relevant definitions of both diagonal matrices, and the pinned `Complex.ofReal_inv` source. The static audit independently bound all 20 prospective proof files to the literal `a6ff104e8a050cf5d22d08e55e1818e0228906ad` Git files and actual run receipt. Nineteen files are byte-for-byte unchanged. The changed source is exactly the composition of these two edits:

1. The Hermitian inverse-diagonal proof explicitly unfolds `inverseDiagonalWeights` and `diagonalWeights`, then uses `Complex.ofReal_inv` to identify the real inverse embedded in the complex field with the inverse of the embedded real. This lemma applies at zero too; no nonzero assumption or mathematical restriction was added.
2. All 17 occurrences of the bare bound identifier `λ` become the fresh identifier `lam`. Existing `hλ` identifiers remain unchanged. The spelling change preserves intended binding and all expressions. Because the before file failed parsing at this token, this is a checked source-level alpha-renaming; I do not claim a comparison between two successfully elaborated syntax trees.

All five local declaration headers agree after this bound-identifier renaming. The 18 public export headers are literally unchanged relative to the actual before Git sources, and all ten frozen files are byte-identical. Two inherited presentation differences from Challenge were inspected explicitly: opened `Filter` names versus qualified names in `radius_one_semantics`, and grouped versus successive existential binders in `rounded_extremal_norm`. Neither is introduced by this patch. Future Comparator execution remains the authoritative elaborated type check.

The exact full source delta was reconstructed by the audit and compared byte-for-byte with the proposed file. Imports, options, trust checks, resource limits, credits, the Complete wrapper, and frozen contracts are unchanged. The proof graph remains closed; no holes, custom axioms, native trust bypasses, or new resource overrides were introduced.

## Actual evidence and limits

The actual run [35094433103](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35094433103), at literal `a6ff104e8a050cf5d22d08e55e1818e0228906ad`, failed. Its diagnostics show the inverse coercion mismatch and bare-`λ` parse errors addressed here. Trust diagnostics from the failed elaboration are not accepted proof certificates. I checked the 20 literal Git source bindings, the corresponding receipt hashes, all eleven command log hashes and unchanged post-command input maps, and the exact Complete/Challenge blobs. The root's separate authenticated 1,957-input audit is retained and hash-bound, not relabeled as my own full-input Git execution.

This review executes only static Python/Git inspection, not Lean, Lake, Comparator, or the Tau Ceti tool. The applicable fidelity, no-statement-weakening, trust, and reproducibility principles were applied manually. The candidate is uncompiled; downstream errors may remain. No CI, branch, PR, status, or count was changed.

## Static-reader correction

The initial review-reader attempt stopped because it demanded literal spelling equality between an already unqualified implementation header and its qualified frozen counterpart. That exact reader and a note are preserved under `preparation-history/`. The completed reader proves literal before/after equality for all exports and permits only the two explicit inherited presentation normalizations described above. No proof or evidence file was modified.

The machine-readable checks and source bindings identify all exact reviewed bytes. The approved author manifest is `8e7e5d86680074a990db36e21047e27b8ea32c721420891c00e4b49a77b40ba7`; candidate closure is `07893741f5266879d52af8a39abe01ea3f56d24243dda7e9a3d8584489b184a5`.
