# MI-04 / MF-07 publication preflight, 16 September 2026

No duplicate formalization or original-target mismatch was found in the checked
public snapshot. Both upstream entries remain **Solved**, not Lean verified.
This is a publication preflight, not acceptance of either candidate proof.
Reviewer: `/root/mi04_independent_referee`. No source, Git, PR, CI configuration,
status or count was changed; no Lean or Comparator ran.

The fresh API interval was **12:15:31–12:15:43 UTC**. It covered all 14 recursively
API-listed public repositories, 252 branch heads, all 153 upstream open/closed
PR records (the fork PR endpoints added none), and 206 complete immutable trees.
Two trees were newly captured; cached trees were individually rehashed. Matching
used problem IDs and related target wording in paths and PR title/body/head
metadata. It does not rule out private, deleted, unpushed, unusually named or
unmentioned comment-only work, or changes after that interval.

Upstream main is still
[`ce47b5630bf3680d9211131c3a43825b022c139a`](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/ce47b5630bf3680d9211131c3a43825b022c139a).
The freshly retrieved [MI-04 canonical page](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ce47b5630bf3680d9211131c3a43825b022c139a/matrix-inequalities-and-norms/MI-04/README.md)
and [MF-07 canonical page](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ce47b5630bf3680d9211131c3a43825b022c139a/matrix-functions-and-stability/MF-07/README.md)
match the frozen source-provenance and current campaign hashes exactly. Their
permanent registry paths are unchanged. Both lack an active canonical Lean
project in the upstream tree.

The relevant historical submissions are merged [PR 6, MI-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/6)
and merged [PR 110, MF-07](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/110).
They credit Matthew J. Colbrook's informal mathematics and do not claim Lean
verification. Merged [PR 149](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/149)
resolves the different MF-06 target and only mentions the existing MF-07 result.
No matching pending or closed formalization PR was found. The sole target-named
Lean tree is our [development commit a6ff104e](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/a6ff104e8a050cf5d22d08e55e1818e0228906ad/.lean-development):
21 MI04 files, 20 MF07 mathematical files plus its Complete wrapper, their
Challenges, and two historical MI04 metadata snapshots. These are our own
development inputs, not competing canonical verification evidence.

The exact original targets still agree with the frozen Challenges. MI-04 asks
the universal PSD block operator-norm premise to imply an affine Hermitian
representation, for every complex matrix and n >= 1. Its final declaration
`NLA.MI04.universal_positive_block_essentially_hermitian` states that complete
implication using the actual Euclidean operator norm and the genuine universal
premise. **Do not describe this export as formal verification of the entire
iff in the earlier informal resolution notice.** No invertibility, simple
spectrum or dimension restriction may enter the publication claim.

MF-07 asks for one positive constant chosen from d before the compact complex
family, covering every positive word length and generator selection at joint
spectral radius one. `NLA.MF07.canonical_uniform_bound` preserves that quantifier
order and scope. Its root-limit and maximum semantics have separate required
exports. The candidate uses `Theta_1 = 1` and
`Theta_d = d (6 d^2 / (d-1))^(d-1)` for d >= 2, via the consumed kernel LeanCert
bound exp(1) <= 3. **Do not claim formal verification of the manuscript's smaller
2e constant, sharpness, general-radius formula, real-field extension or separate
MF-05 theorem.** This enlargement still answers the full original existential
question. Existing informal claims and authorship must remain attributed.

## Exact remaining publication work

The accepted campaign example is [IE-13 PR 281](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/281),
observed **open, unmerged, mergeable/clean** at literal head
`b106102c68cbc77adbed1c79c0dbf93bb0054df7`. Its separate proof commit is
`032d4c86c52ffde0c4d440f28527ba43555a0a24`. Its 184 project inputs and seven
external document/index changes total 191 PR paths. Actual proof, publication
and upstream runs were separately accepted in the campaign; that does not
mean upstream main has merged the PR.

For each problem, use its existing canonical directory and a **separate PR**:
`matrix-inequalities-and-norms/MI-04/lean/` or
`matrix-functions-and-stability/MF-07/lean/`. The requirements come from
[the current Lean contribution rules](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ce47b5630bf3680d9211131c3a43825b022c139a/CONTRIBUTING.md#lean-verification)
and [the per-problem workflow](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ce47b5630bf3680d9211131c3a43825b022c139a/docs/lean/README.md).

1. Obtain and audit actual successful development evidence for the exact final
   graph. Freeze/source/repair reports are not compilation evidence. Preserve
   all 21 MI04 or 18 MF07 contracts and every proved dependency. Finish two
   current nonauthor complete-source review chains. Root and this reviewer
   have implemented MI04 repairs, so their narrow reports must not be relabeled
   as two wholly independent final proof reviews. MF07 repair authorship and
   statement-author roles likewise need their existing explicit disclosures.
2. Prepare the self-contained project: all actual mathematical sources,
   `Solution.lean`, unchanged `Challenge.lean` and Definitions, `comparator.json`,
   `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `LICENSE`,
   `NUMERICAL_TARGETS.md`, `SourceCorrespondence.md`, `SOURCE-PROVENANCE.json`,
   `STATEMENT-FREEZE.json`, actual implementation/source map, README and v0.4
   `formalization.yaml`. Record any build-only wrapper/default-target adaptation.
   Retain exact statement receipts/logs and referenced frozen snapshots, useful
   source reviews, source/packaging manifests and privacy-screened originals;
   link and hash any contact-bearing omitted original instead of rewriting it.
3. Independently review the exact canonical package, run the unchanged schema
   validator, and obtain a fresh non-root Linux project run. Authenticate
   literal checkout, all input/pre/post hashes, all 21/18 Comparator matches,
   default-kernel replay, transitive permitted axioms, LeanCert kernel trust,
   rejection tests and sandbox/service controls. Retain dated raw logs,
   receipt/result, source lock and independent runtime reviews in `verification/`
   and `reviews/`. A development run has no Comparator and cannot replace this.
4. Only after canonical acceptance, update the canonical `README.md`,
   `problem.tex`, `problem.pdf`, existing `RESOLVED.md` entry, category README,
   root `README.md` and `CATALOG.md`, plus the lean README/yaml/evidence links.
   The canonical README **and RESOLVED must link the immutable tested proof**.
   Preserve the original mathematical target and manuscript; visually inspect
   every regenerated PDF page. Validate IDs against the published base,
   regenerate indexes and run the existing 17 permanent-ID tests. No renumbering
   or weakening of safeguards is permissible.
5. Independently review the exact publication overlay, then audit another run
   on its literal final published commit. Open each new PR against
   `ajt60gaibb/OpenProblemsInNLA:main`, request inclusion in main, and authenticate
   the actual upstream run and its possible synthetic-merge checkout. Keep
   proof-commit, publication-commit and upstream-checkout identities distinct.
   Only actual accepted evidence may support a campaign count/status update.

Every public file must preserve Colbrook's mathematical credit (Cambridge DAMTP)
and credit George Stepaniants's formalization with the Department of Computing
and Mathematical Sciences, California Institute of Technology. Preserve licenses,
reuse credit and AI-agent disclosure; publish no contact email. No blocker from
duplicate work or target drift was found. The remaining blockers are the actual
proof/runtime, final referee, canonical package and publication gates above.
