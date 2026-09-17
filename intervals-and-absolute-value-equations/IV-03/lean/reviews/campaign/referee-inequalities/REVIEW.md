# Independent full-source review of IV-03

**Verdict: approve the full mathematical formalization for a fresh campaign rerun.**
This is a nonimplementing review by `/root/mi04_independent_referee`, an AI
agent. I read all fourteen active Lean inputs (1,216 lines, including the
statements-only Challenge), the complete original canonical problem, and the
complete Colbrook manuscript. I did not edit the author's proof, execute Lean
or Lake locally, publish anything, or change a completion count. I read the
first referee's report as context, then independently inspected the full proof
and ran the source/evidence audit retained here; I did not execute the first
referee's audit program.

The mathematical argument is **Matthew J. Colbrook's**. The existing
formalization is **Sidney Holden's**, with disclosed AI assistance and the
retained Apache-2.0 license. This review does not transfer their authorship to
the campaign's submitter or reviewers.

## Exact boundary and immutable sources

The published source is `sidneyholden1/OpenProblemsInNLA`, branch
`codex/lean-iv03`, commit
`281f440650d174602120ca9b2b930d38f9fef205`. The historically tested commit is
`516ad4a0e85c21c7ef34507db9ab3b68b393bb90`. All fourteen active Lean inputs are
byte-identical at those commits. The only differences among the 75 project
inputs are `README.md` and `formalization.yaml`, which record later status.
`ALL-75-INPUT-BINDINGS.json` matches every tested input to the actual receipt
and immutable Git blob, and every published input to its immutable Git blob.
`ALL-14-SOURCE-BINDINGS.json` binds each full source read and retained here.

The canonical README and full manuscript match the retained upstream Git
objects at `deb549fa9ddd6b119e6c59016f268237e645dfa2`, with hashes respectively
`c5c92b828ae968b01e53dab0e71b9adca662efe0075f8928606dc5e671c439d2` and
`f09cb222b822704855031d18c971b3d61dbea4a371ee4547414c9e40500c3e98`.
The original problem ID, canonical path, and target are unchanged.

The four public exports have exactly the four Challenge headers, including
all binders, hypotheses and conclusions. Neither file has ambient section
variables that could introduce an unnoticed typeclass parameter. All seven
frozen input hashes and both frozen statement-review hashes match. Challenge
contains four deliberate placeholders and proves nothing; the thirteen-file
Solution closure does not import it or any historical audit consumer.

`IsInverseM A` requires `IsUnit A`, entrywise nonnegativity of `A`, and
nonpositive off-diagonal entries of `A⁻¹`. This is the stated inverse of a
nonsingular M-matrix. The `IsUnit` guard is essential and present: Mathlib's
totalized inverse at singular matrices cannot make the property vacuous.
`intervalFamily` quantifies over all independently varying closed entrywise
interval members. `OrderedEndpoints` is exactly `L ≤ U`. The sign vector is
minus one at its selected index and plus one elsewhere, and `vertex_formula`
proves the pointwise vertex is exactly `C + s • (Dᵢ R Dⱼ)`.

The final equivalence quantifies over every `n ≥ 1`, all real endpoints,
every ordered pair of indices and both signs. The stronger negative-sign
`nSquaredCriterion` is also proved. No symmetry, positive width, strict
entrywise positivity, irreducibility, diagonal dominance of interval members,
or interval regularity appears as a premise. The source manuscript's
complexity discussion is outside the original equivalence and is expressly
not claimed formally.

## Independent proof-path assessment

1. **Weighted Z-matrix foundations (`Proof`).** From `A A⁻¹ = I`, off-diagonal
   signs give `1 ≤ Aᵢᵢ (A⁻¹)ᵢᵢ`, hence both diagonal entries are strictly
   positive. The row-sum vector `w = A 1` is strictly positive and satisfies
   `A⁻¹ w = 1`. The weighted maximum principle takes a minimum of `yᵢ/wᵢ`;
   a negative minimum contradicts `By ≥ 0` and `Bw > 0` with the correct
   reversal when multiplying by nonpositive off-diagonal coefficients.
   Applying it to both differences proves injectivity, then genuine matrix
   invertibility, and then nonnegativity of inverse columns. Determinant
   positivity uses the nonsingular homotopy `(1-t)I+tB` and the intermediate
   value theorem. Removing off-diagonal nonpositive weighted contributions
   proves principal-block versions, including the empty block.

2. **Principal and Schur closure (`Principal`).** An arbitrary finite index
   embedding is completed by enumerating its complement; it is not restricted
   to leading submatrices. Both full and eliminated block inverses are derived
   before Mathlib's block inverse formula is used. For the principal block of
   `A`, its inverse is the Schur complement of `A⁻¹`, whose off-diagonal signs
   are proved from two nonpositive cross blocks and a nonnegative eliminated
   inverse. The dual construction proves principal Schur complements of `A`
   are inverse-M. The transfer identity `QD⁻¹ = -E⁻¹F` follows from actual
   inverse block equations; its signs are established, not assumed. Transpose
   yields the other transfer block. There is no circular principal closure.

3. **Complementary minors and adjugate completion (`Complementary`,
   `Adjugate`).** The complementary determinant identity is proved from block
   inverse and determinant formulas with required invertibility established.
   For a negative determinant, every nonempty inverse principal minor is
   negative because the complementary original minor is positive; the empty
   complementary determinant is one. For singular `A` of order at least
   three, a codimension-one minor forces rank at least `n-1` and
   `A adj(A)=0` forces adjugate rank at most one. A positive-diagonal Z-matrix
   of order at least three cannot have rank at most one: the relevant two-by-two
   minors would require two strictly negative entries whose positive product
   equals a nonpositive product. Thus singularity is excluded without assuming
   it away. If `det A < 0`, a three-by-three principal inverse block has
   negative diagonal, nonnegative off-diagonal, and negative two-by-two
   principal minors. The explicitly proved determinant inequality makes its
   determinant positive, contradicting the complementary-minor identity.
   Consequently `det A > 0` follows from the stated proper-minor and adjugate
   conditions. No desired conclusion is smuggled into a definition.

4. **Cofactors and exact comparison (`Cofactor`, `Monotonicity`).** Replacing
   row `j` by coordinate vector `i` gives `adj(A)ᵢⱼ`, with the indices oriented
   correctly. Eliminating the invertible complementary block leaves a two-by-two
   determinant equal to the negative off-diagonal Schur entry, proving
   `adj(A)ᵢⱼ = -det(D) Sᵢⱼ`. Only `D` is assumed invertible; `A` need not be.
   The noncommutative resolvent identity
   `D⁻¹-E⁻¹ = E⁻¹(E-D)D⁻¹` is correctly ordered. The bilinear difference is
   decomposed into three entrywise nonnegative products, with each sign premise
   used explicitly. This exact algebra replaces the manuscript's differentiation
   and avoids interval grids, approximation, or a hidden global smoothness
   premise.

5. **Whole-interval bridge (`IntervalStructure`, `SchurInterval`,
   `IntervalAdjugate`).** Vertices commute with every principal embedding.
   The transfer-sign lemma uses a proper block containing one retained index
   and the complementary indices. Three explicitly constructed hybrid matrices
   stay inside the original full interval; their proper principal inverse-M
   properties supply all four transfer signs needed by the resolvent comparison.
   These facts yield the Schur entry at any interval member at least as large
   as the tested negative-sign vertex entry. That vertex's Schur complement
   is nonnegative by proved closure. The cofactor identity therefore gives all
   off-diagonal adjugate signs for the arbitrary member, including a member
   whose invertibility has not yet been established.

6. **All dimensions and exports (`Vertices`, `IntervalInduction`,
   `Solution`).** The one-dimensional case uses the positive lower endpoint.
   The two-dimensional case compares diagonal and off-diagonal products using
   proved nonnegativity and the actual positive determinant of the tested
   corner. Strong induction handles all proper principal intervals, with the
   empty matrix treated explicitly. Only then does adjugate completion prove
   invertibility of the arbitrary full member. Necessity follows from actual
   vertex admissibility, and the negative-sign criterion implies the complete
   two-sign sufficiency. Zero widths, repeated vertices, zero entries and
   reducible matrices remain valid throughout.

I found no mathematical correction required. The named primary Mathlib APIs
were inspected in their exact pinned source and byte-compared to local Git at
`0df444a360eaa60ab8c11dca51a86af692955474`: matrix inverse and unit definitions,
rank restriction/nullity, adjugate row replacement and reindexing, block inverse
and determinant formulas, and the closed-interval intermediate value theorem.
`PRIMARY-API-BINDINGS.json` records those sources and inspected line intervals.

## Actual runtime evidence and its limits

The historical Linux run is
`https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34926260380`,
job `104244928525`, at the tested commit above. I independently re-fetched
GitHub's run, job and artifact metadata. GitHub identifies artifact
`10380345663` with SHA256
`bef757bd594f82e327625b5bcbcc3c395e6d64e3764c95f926a25ffe95337177`;
the retained ZIP has that digest and every extracted file matches it. The
receipt hash is
`50494ef3df157aa2b69cdbc6c9f6a00d568be6d64e80678686be974f0393bfa7`.
All 75 receipt inputs match the tested immutable Git tree, rather than merely
matching a README's description.

The actual Comparator log builds Challenge separately, builds all thirteen
proof-closure modules, reports all four exports' only axioms as `propext`,
`Classical.choice`, `Quot.sound`, and records default-kernel acceptance followed
by Comparator success. Solution contains four actual LeanCert kernel-trust
commands. This is meaningful LeanCert use for a symbolic theorem; no numerical
interval certificate or subdivision is needed or claimed.

The per-project logs also contain honest kernel acceptance, invalid raw proof
rejection, quotient post-check rejection, all five Comparator regressions,
`sorryAx` rejection, and native-computation axiom rejection. The actual statement
mismatch regression fails as intended. The sandbox logs show non-root UID 1001,
separate build/export modes, read-only outer files, denied export writes,
unreachable host loopback, denied AF_UNIX socket creation, rejected nested
namespace write attempts, and four malformed-option rejections. Every substantive
line in these six artifact logs is corroborated by the retained raw GitHub job
log, not just a final green status. A separately skipped workflow controls job
does not negate the controls visibly run inside this successful project job.

I inspected the tested harness's snapshot, immutable dependency validation,
unchanged-input checks, control invocation and final Comparator invocation. Its
source-lock hash matches the receipt, and all retained harness files match the
tested immutable Git tree. The receipt pins Linux Lean 4.33.1, Mathlib, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` and the Forsythe checker tooling.
This is not a new exhaustive security review of Lean or GitHub.

**The fresh campaign rerun remains pending.** I independently authenticated
the historical execution and reviewed the exact unchanged proof bytes; I did
not launch a new proof execution. A campaign acceptance or count change must
still wait for its required fresh controlled rerun on the integrated exact
commit. GitHub, the runner and the pinned toolchain remain trust dependencies;
these checks do not establish that any CI system is impossible to fake.

## Scoped Tau Ceti assessment

Fidelity, correctness, generality and edge cases are covered above. The proof
uses existing Mathlib matrix/rank/block APIs rather than postulating analogous
facts. Exact endpoint algebra and a resolvent identity minimize computation.
Definitions and filenames expose the actual matrix theorem, the import closure
is acyclic, and the public API contains the four frozen targets with no
definition exceptions. Comments explain the singular case, transfer-sign bridge
and algebraic departures from the manuscript. Metadata preserves author credit,
license, AI assistance and honest exclusions. Retained statements-only and
pending-phase notes are historical, while current status points to a specific
actual run. The repository's adapted review protocol is used; neither official
Tau Ceti endorsement nor external human peer review is claimed.

The reproducible Python audit, exact full-source copies, source/header/freeze
maps, primary-source copies, retained actual logs and independently fetched API
metadata are sealed by this packet's `MANIFEST.json`. No proof implementation,
repository identity, Git state or campaign ledger was changed.
