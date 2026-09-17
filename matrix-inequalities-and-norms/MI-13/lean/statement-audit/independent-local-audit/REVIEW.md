# MI-13 local statement elaboration audit

**Pass for a frozen proof handoff, pending the coordinator's independent acceptance.**
Reviewer `/root/mi13_statement_freeze` did not author the MI-13 statements,
either independent statement review, the compiler runner, or the recorded local
run. This review authenticates the retained local elaboration evidence and its
statement prerequisites. It is not a third complete mathematical statement
review, a proof review, proof-implementation authorization, or target acceptance.

The executable read-only audit completed with **585 checks passing and 292
external file bindings**. It reauthenticated all 138 bindings from the two
statement reviews. The script writes only this new review directory; it does
not invoke Lean, Lake, Git, a cache builder, or the network. No mathematical
source, original draft, canonical page, public status, or count was changed.

## Exact evidence

| Record | SHA-256 |
| --- | --- |
| Original draft manifest | `388c3556730a9fc132ac7cd2f72493b468f233d6e683dba74d69b9d40fd972c7` |
| Definitions | `add61115ca2d92951bfc479c3de4dcbb9f2b850cac2ab793cf0dcf543e75622b` |
| Challenge | `6fc6f34a1a559097379921a8237c1b23ea15c67ff7bf23b7ffd60ff3d107f088` |
| Numerical-first record | `1676285e543d2cf9e1d9d01bc8767109b87c68fc86adc8ab91990a659b001f12` |
| First statement review manifest | `d13fd9a5bb8eb32a34fab8d65d585e68f3d7dafae8bde8b55ab6cbcd7b9c0a54` |
| Second statement review manifest | `d6836fcabf01d3d0a0694a365ac3abcbcb72f90714f8ea724a0d1075f045683f` |
| ASSEMBLY-20.json | `e1f54dff4502e507061927e27802cd51c001e6c26e3eb13e543accbb128039f6` |
| development-20 receipt | `2c8e42dd19f2ae562bb8c7459071ec9ba9f15718a9bbdefc76fbffe09386becc` |
| Actual serial runner | `d6c00e953688e155c0a313a8f49c7c395ad0fb1166faf3655c0b47f3ea2b2266` |
| Actual compiler binary | `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` |
| This audit result | `1c31349c3f5a3073e4c37dce89367527f1759e459ae866682d7d458e7d337773` |

The actual run took place in
`/private/tmp/nla-lean-local-shared-20260916`, on macOS. Both commands used
`/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`
with `--threads=1 --memory=4096 -o <recorded output> <recorded source>`.
The complete argument vectors, working directory, start/end times, source
hashes, log hashes, dependency output hash, and output hashes are retained in
the copied receipt. They are actual invocations, with no reused-output status.

| Module | Exit | Elapsed seconds | Output SHA-256 |
| --- | --- | --- | --- |
| `NLA.MI13.Definitions` | 0 | 17.461387208895758 | `5700c6f53f2511cd2865956461d692c7ad09f6f6fd884c73670c3bf2be54ba96` |
| `NLA.MI13.Challenge` | 0 | 3.9612790839746594 | `5a2ffcc358e6fffc54c684ddce7de5a9dcc5ea18cc65479786d1553f30ed5201` |

The Definitions log is empty. The Challenge log is exactly 36 `sorry` warnings,
one at each declared theorem's source line. It contains no other diagnostic.
The second command consumed the exact successful Definitions output above.
Both current outputs were rehashed and copied into this review's private
evidence directory. These binary copies are evidence only; do not place them
in the canonical project or use them as Linux verification output.

## Source and dependency audit

All 54 entries of the original manifest still match, and the original draft
contains exactly those files plus its manifest. Its only active Lean files are
Definitions and Challenge. Every complete header and header hash agrees with
the stored list. Comparator selects all 36 names exactly once, has no
definition holes, and permits only `propext`, `Classical.choice`, and
`Quot.sound`. The separate Solution module does not exist.

The original Challenge was copied byte-for-byte to
`NLA/MI13/Challenge.lean` for the shared local runner. No source alteration was
needed for elaboration. The canonical project-level `Challenge` target was
not separately built. The source bytes and declaration namespace are the
same; this path transport does not constitute a final Comparator check.

The assembly and receipt agree on all 116 shared source hashes. All 116 local
files still match. Compared with assembly 19, the only additions are the two
MI-13 files; all 114 prior records are unchanged. The assembly binds both
independent statement review manifests, and their retained timestamps precede
assembly and execution. The numerical-first record binds the unchanged
numerical boundary and concrete plan before the recorded draft stage. That
chronology is a consistency check of sealed records, not independent evidence
of filesystem creation time.

The project and local Lake manifests have identical dependency records for
all ten packages. The actual dependency HEAD files agree with all ten pinned
revisions. Lean is pinned to 4.33.1, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert to
`621a43d7cf21f87872392a01e874f2f1dbddc926`. All ten retained primary-source
snapshots still match their actual pinned source files. The six direct
Mathlib import sources and cached output hashes were recorded anew in
`DEPENDENCIES.json`. No global library absence search or fresh cache build
was performed.

The original receipt binds the compiler and runner hashes, local source
hashes, and local dependency output; it does not bind the environment JSON or
external cached output hashes contemporaneously. This audit records their
current retained state, not a new runtime measurement. Final fresh Linux
verification remains necessary. The old environment record also retains an
early 2048 MiB policy sentence; the actual runner, arguments, assembly and
receipt consistently use the user-authorized 4096 MiB limit. The runner has
an advisory lock, one-thread environment setting and sequential subprocess
calls. This establishes its execution design and the recorded sequential
commands, not an independent historical census of every machine process.

## Read scope and handoff constraints

I read the complete canonical MI-13 page, all Definitions and 36 contracts,
numerical boundary, source correspondence, review plan, metadata, both complete
independent statement reviews, and the actual serial runner and logs. The
original statement remains the complex rectangular inequality for every
`m,n >= 2`, all ranks, the exact coefficient two, the actual operator and
Frobenius norms, and the first two ordered singular values. Neither the SVD
nor Audenaert's refined commutator theorem has been assumed in the final target.

I read the retained Tau Ceti review guidance and attribution, correctness,
generality, proof-quality and reuse rubrics at
`afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, and Comparator guidance at
`2312244ac716564a61cc0bf4e107d9abf1757a61`. The two nonauthor statement reviewers
remain `/root` and `/root/ra02_full_final_referee`; the author is
`/root/mi04_independent_referee`. These are AI-agent reviews, not human peer
review or official Tau Ceti endorsement. This audit does not upgrade their
scope into proof review.

The frozen handoff must preserve the exact mathematical files, numerical
targets, all 36 headers, dependency pins, license, and attribution. Any
mathematical boundary change reopens independent statement review. Proof
development remains local first, coordinated through at most one compiler
process with one thread and a 4096 MiB cap. Reuse only pinned caches and exact
source-matched successful outputs. The planned half-positivity LeanCert
certificate must use explicit kernel trust and be consumed by averaging.
No certificate has run here. Keep all other algebra symbolic and retain the
zero, deficient-rank, repeated-singular-value and empty-helper cases.

Two nonauthor final proof reviews and fresh real non-root Linux
Comparator/default-kernel/sandbox/rejection-control checks on all 36 contracts
remain later gates. No final proof, Linux run ID, measured axiom report,
published commit, canonical `Lean verified` status or count increment exists
for this task. George Stepaniants retains the Department of Computing and
Mathematical Sciences, California Institute of Technology credit, without
email; Nobori, Audenaert and repository contributors retain their prior roles.
