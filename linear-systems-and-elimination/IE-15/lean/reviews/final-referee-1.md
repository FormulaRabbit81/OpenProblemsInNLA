# IE-15 final source referee 1

## Verdict and scope

**APPROVE the complete proof source, complete-target correspondence, local reproducibility and inspected kernel-trust checks at the exact input hashes below. No material findings.** Authoritative sandboxed Linux Comparator execution and its final artifact binding remain pending. This report does not claim Comparator success or authorize promotion to **Lean verified** before that required evidence is obtained and checked.

Reviewer: independent OpenAI Codex AI agent `/root/reference_api_review`, 2026-09-15. I authored no proof code and did not author the mathematical dossier or statement boundary. I independently approved the pre-proof boundary, then read every actual proof module and the final exports. This is AI-agent review, not human peer review or official Tau Ceti endorsement. The review applies the repository's adaptation of Tau Ceti correctness, scope, attribution, reuse and quality standards at [rubric revision 603b28011f779bd341d0a08e788498b81542bd7d](https://github.com/TauCetiProject/TauCetiReview/tree/603b28011f779bd341d0a08e788498b81542bd7d).

## Exact input binding

Paths are relative to this Lean project. I rehashed the live project after reviewing and testing the isolated source snapshot; all eighteen proof/statement/build inputs still matched. README and metadata were separately read and hashed at the stated pending-Linux stage.

| Input | SHA-256 |
|---|---|
| `Challenge.lean` | `2193762b8e25272342703e34d8246a4a5901dd0cdb0eec71f30ad97ccf5186b9` |
| `NLA/IE15/Basic.lean` | `1df00296842bb5970508912dbd52834f308e930dc5e9cce023d203b41a53033a` |
| `NLA/IE15/Coordinates.lean` | `a889559725d1faab768d21c109b4e3ce4500cc13a88f52b22afccf04c8908de3` |
| `NLA/IE15/Definitions.lean` | `8d43a24d1aba8dfd616a66a49463d0bb4bee798c1dd904c2bf7614a5e4bb90ab` |
| `NLA/IE15/FourthScalar.lean` | `3c55e8dc0d253a726aa7963d087b13bdfbaf1b547a56a0ebb03507aca20a30af` |
| `NLA/IE15/Normalization.lean` | `f1cc699adda5e90b52535b0c87cd7d1296846846b8505884b3de6ea383a79561` |
| `NLA/IE15/NormalizedBounds.lean` | `7729ea53628cbecc2a9df1b8edc6e4c0c7ce6cf65b58c9e7c70d4b2ce7ccdff4` |
| `NLA/IE15/Permutation.lean` | `d6f8fed5f353f9f45156ec3ea99f05273337557ddff13c8c066fc775ec393de5` |
| `NLA/IE15/Proof.lean` | `2ddefbb9f31483c448295316b55b6f8a32b8d0d9bbfd0d21610fe1b54fba7e91` |
| `NLA/IE15/Reduction.lean` | `8fe71ed25fa107e48e12f8c18bd76b1e6fcb90f7dbe9e82b3fcd25953d0d962c` |
| `NLA/IE15/Scalar.lean` | `5acf89a5f311819c151399299bebcfdc8602b7c466b7473652584fce65d509aa` |
| `NLA/IE15/Witnesses.lean` | `1ef349f423ffa8bab7d55fba3662417a3cbd9a5ccd4a94819db4fadaaf0f2241` |
| `NUMERICAL_TARGETS.md` | `36a0149348cad5c9e71bc18b506df384d0641470cb70510add53871129ee4546` |
| `README.md` | `c39c5266389dd685a19ba2ef4f14196c2951f6cf01c3aa315d8d02345199948e` |
| `Solution.lean` | `c1b05e5ead668de2133da70178a632aa69ff2125418cb159a2e597de711291eb` |
| `comparator.json` | `5198b3f85a070ce13298ee7af09cfef9984e0a932eb888e62fd4213634893b7a` |
| `formalization.yaml` | `fde8b1dc1b7bed55f969313054a31a242f68d7aaff1e65aafde2cfaf812b96fe` |
| `lake-manifest.json` | `870a86a98be8aef373fc3461f690535afbd67d33a44f210c488e65fabe2d9a06` |
| `lakefile.toml` | `2dd26d1f3978d85910a8572d3cf0d62ef98f01a82b1d3674117dad62ea2962bb` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The unchanged canonical README and original solution hashes are retained in [statement-referee-1.md](statement-referee-1.md). They identify the complete original IE-15 target at published source base `c7f399b1694e0a68756e8d060e2a71775c044301`; no ID, canonical path or mathematical statement was changed by this proof. A subsequently reported origin/main update concerns unrelated IE-18 attribution and rendering; this review does not infer anything about those unseen changes.

### Environment change since pre-proof approval

I explicitly compared `lakefile.toml` with the pre-proof reviewed copy: its only change is `defaultTargets = ["Challenge"]` to `defaultTargets = ["Solution"]`. LeanCert and all dependency revisions are unchanged. The new default builds the complete proof; Comparator still explicitly names distinct Challenge and Solution modules. This environment change is approved. The original `Definitions.lean`, `Challenge.lean`, dossier and manifest bytes remain exactly those independently approved before implementation.

## Complete mathematical correspondence

The final eight public declarations match all eight frozen Challenge signatures. They retain every real nonsingular input, all row/column rook choices, all weak tie inequalities, every intermediate active entry, exact rational attaining witnesses and both actual real supremum equalities. The exported determinant binder was renamed `_hA`; its mathematical hypothesis is unchanged. The proof's upper bound actually works for every complete admissible path without needing that extra determinant hypothesis. No conclusion is hidden in a new assumption or a vacuous structure.

- **Actual arbitrary paths.** `Permutation.lean` constructs the global row and column permutations from the literal future swaps, proves future swaps fix earlier indices, and proves equality of the two trajectories up to those future permutations. It separately proves preservation of admissibility and every active maximum. This discharges the full all-path reduction; diagonal-path coordinates are not substituted for the canonical model without proof.
- **Normalization.** `Normalization.lean` proves Schur covariance under nonzero diagonal row/column scaling and then proves every stage's magnitude scales by the positive original entry maximum. Unit signs remain nonzero even when a lower multiplier is zero. The constructed row and column signs simultaneously make every pivot positive and the chosen last-row lower multipliers nonnegative. All these facts are proved from actual admissibility, rather than assumed for the original input.
- **Coordinate reconstruction.** `Coordinates.lean` defines pivots and multipliers from genuine diagonal Schur trajectories, derives nonzero denominators and row/column magnitude bounds from admissibility, and reconstructs each original entry by induction over the actual rank-one updates. There is no assumed LDR factorization or missing reconstruction theorem.
- **Full signed scalar inequality.** `Scalar.lean` retains the reviewed p,q,a,b,c1,c2,d1,d2 domains and the three original-entry inequalities. Its sign cases are exhaustive. The final case replaces the manuscript's piecewise Phi monotonicity by the exact polynomial inequality `scalar_product_bound`; expanding `(2-q)*(2-q*x*y)>=0`, together with `(q*x)*(q*y)<=U*V`, proves it on the whole required box. No continuous domain is replaced by samples, an optimizer or interval heuristics.
- **Order-three and order-four analytic bounds.** The signed scalar h inequality yields W<=2 directly: use p+q>=2 in the h bound, or bound each c*d<=1 when p+q<2. Thus the formal proof does not need to assume a principal submatrix nonsingular or formalize the manuscript's singular-final-value detour. `FourthScalar.lean` retains full signed d1,d2,D,u,v domains, handles D<=0 directly and proves the D>0 bound by nonnegative bilinear interpolation weights. `NormalizedBounds.lean` derives every scalar constraint from the original matrix entries and the proved reconstruction identities. The original bottom-right entry need only be <=1, so no replacement of that entry is required. These are genuine stronger intermediate arguments, not weaker target statements.
- **Every active entry.** `Reduction.lean` combines the normalized final-pivot theorem with the original trajectory's factor-two bounds at each earlier stage. In the last active block only its one diagonal entry remains. It transports the last-stage bound through the proved permutation and scaling equalities, then bounds each entry by its active maximum. Orders three and four instantiate all residual analytic obligations in `Proof.lean`.
- **Attainment and supremum.** `Witnesses.lean` proves exact padded Schur matrices, determinants 3 and 70/9, admissible pivot inequalities including ties, initial maxima one, stage maxima `(1,2,3)` and `(1,2,3,14/3)`, and the attained ratios. The greatest-element proofs use these actual witnesses for membership and the complete universal bounds for maximality. The final theorem derives both `sSup` equalities from greatest elements and explicit nonemptiness; it does not exploit an empty or unbounded real supremum convention.

## Independent execution and trust inspection

I copied the complete project source to `/private/tmp/nla-campaign-final-review1/full-snapshot`, with a fresh project build directory and only the pinned dependency cache shared through `.lake/packages`. With Lean 4.33.1 explicitly selected, my own `lake build Solution` exited **0**, built every project module and Solution, and reported **3641 jobs with no warnings**. The complete output and command/exit record are [full-solution-build.log](final-referee-1-evidence/full-solution-build.log) and [full-solution-build.json](final-referee-1-evidence/full-solution-build.json). This is an independent local macOS source build; it is not the pending Linux sandbox or kernel-export replay.

I also ran the retained [AuditFull.lean](final-referee-1-evidence/AuditFull.lean), which assigns the proved exports to all eight exact signatures copied from the previously reviewed Challenge and checks transitive axioms/kernel trust for fourteen declarations: all eight exports, the LeanCert certificate, permutation/normalization existence bridges, both normalized final-pivot bounds and the all-entry reduction. Every exact-signature assignment and every `#assert_trust kernel` passed; every printed axiom set was exactly `propext`, `Classical.choice`, `Quot.sound`. See [audit output](final-referee-1-evidence/full-signature-axiom-audit.log) and [command/exit record](final-referee-1-evidence/full-signature-axiom-audit.json). To rerun in this project after building, use `lake env lean reviews/final-referee-1-evidence/AuditFull.lean`.

The initial reviewer audit omitted explicit arguments when applying three theorem constants and therefore failed; I corrected only the reviewer-owned audit file. No candidate input changed. The corrected retained run exited 0; original diagnostic files remain in the scratch review directory. This was a reviewer-script error, not a proof repair.

The separate scalar-side review and its fresh-build/ten-declaration axiom inspection are summarized in [scalar-review.md](final-referee-1-evidence/scalar-review.md). Source scans of all solution modules found no sorry, admit, custom axiom, native_decide, native-compiler axiom reference, unsafe declaration, implemented_by or kernel-bypass setting. `Solution.lean` imports only the complete Proof module; the eight deliberate Challenge placeholders are outside its import closure.

The LeanCert certificate `four_le_fourteen_thirds : (4 : ℝ) ≤ 14/3` uses both the file setting `leancert.trust "kernel"` and the explicit `(trust := kernel)` invocation. Its proof is actually consumed by the order-four all-entry bound. All nine public/certificate trust assertions also run in `Proof.lean`. Exact rational witness arithmetic and polynomial scalar inequalities use ordinary kernel-checked Lean tactics; no unproved numerical premise is introduced.

## Reuse, attribution and current-stage metadata

All implementation headers credit the original George Stepaniants resolution and substantial Codex assistance, with the requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation and no contact email. Definitions/Basic credit the retained IE-05 design. Mathlib's standard finite suprema, determinant, permutation and ordered-field APIs are used. Searches did not locate a direct replacement for the problem-specific signed scalar or rook-trajectory constructions. The short bilinear interpolation lemma has direct consumers and avoids importing an unnecessary optimization development. Source simplifications are explicitly documented rather than described as a literal translation of the manuscript.

I read `README.md` and `formalization.yaml`: the eight results, zero solution holes, axiom lists, AI roles and original proof attribution agree with the inspected source. The metadata correctly distinguishes Schiffer/Forsythe structural/API reference from proof authorship, identifies IE-05 adaptation and keeps the unrelated Colbrook order-five construction outside this target. It asserts neither author endorsement nor external human peer review. Its current pending-final-review/pending-Linux wording was truthful when written; after both final reports are accepted it may be updated to say source review passed while Linux remains pending. The canonical status remains **Solved**. I did not run a separate metadata-schema validator in this pass.

## Remaining gate

Before promotion or a claim of complete verified publication, require a fresh authoritative non-root Linux run of the pinned shared harness, its successful sandbox/replay/negative controls, all eight Comparator targets, the exact three-axiom allowlist, and binding of logs and reviewed statements to the committed candidate. New proof-source bytes require renewed source review; changed statement bytes require renewed statement review. This approval covers only the exact inputs above and the executed checks documented here.

```json
{"verdict":"approve","summary":"Complete IE-15 source preserves the frozen all-path, all-entry target and passes independent fresh local compilation, all eight exact-signature assignments and fourteen foundational-axiom/kernel-trust checks. Authoritative Linux Comparator evidence remains pending.","findings":[]}
```

## Stage-wording supplement — 2026-09-15

**APPROVE the documentation-only stage update.** I read both updated files, compared their exact diffs with my reviewed copies, read the second independent final-source approval, and rehashed all eighteen proof/statement/build inputs: no mathematical or build input changed. Both independent source approvals are now complete; authoritative Linux Comparator verification remains pending, and the canonical status remains **Solved**. The revised wording states exactly that and makes no premature verification claim.

These hashes supersede only the corresponding documentation rows above:

| Updated input | SHA-256 |
|---|---|
| `README.md` | `26e1e0bd264bcee4b60993e2efd74c9fbb74af53b8db1c5dca25ef6b0712e141` |
| `formalization.yaml` | `fadea81f62bfe64c52c74eec5b6bc8019c6f27bb80f266ba6a55305fc8d0d7f7` |

The second referee report inspected for this stage claim had SHA-256 `ad7ac5a2e1f20f15afe96d651cbe9907965c57785a5bf05aa071da2ba771eb64`. This supplement adds no Linux/Comparator approval; I will inspect the actual candidate-bound execution artifacts separately when supplied.
