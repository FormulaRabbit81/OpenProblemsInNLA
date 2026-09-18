# MF-18 — full complex Green-function rank equality

This development proves the complete original MF-18 target. Root's actual
macOS local340 check passed for all 38 proof modules and all 25 frozen contracts
(28 fresh compilations, 10 authenticated source-matched successes). Local341
independently elaborated the Challenge and Solution types and checked the actual
proof-body dependency route to the kernel-mode LeanCert certificate. Both
nonauthor proof reviewers approve the exact source continuation.

**Complete immutable proof verification passed.** All 25 contracts passed [non-root Linux run 35315336123](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35315336123/job/105505732924) at proof commit `0d3a658789510d3cdd14729f22165219f7e7eaf8`. The [retained Linux evidence](verification/linux-2026-09-18/README.md) binds every input and the real Comparator, default kernel, permitted axioms and per-project controls. Publication and PR merge checkouts remain separate gates before campaign acceptance. The machine-readable status is [STATE.json](STATE.json).

## The original target

Let $n\ge1$, let $C,D,R,P\in\mathbb C^{n\times n}$, and suppose $R,P$ are
Hermitian and

```math
P+\lambda D^*+\lambda^{-1}D\succ0\qquad(|\lambda|=1).
```

For every real $\eta>0$, let $X_\eta$ be the unique nonsingular stabilizing
solution of

```math
X_\eta+(C^*+i\eta D^*)X_\eta^{-1}(C+i\eta D)=R+i\eta P,
\qquad \rho\bigl(X_\eta^{-1}(C+i\eta D)\bigr)<1.
```

Assume its finite right limit $X_0$ exists and is nonsingular. Assume
$\lambda^2C^*-\lambda R+C$ is a regular matrix polynomial and that its
unit-circle roots are algebraically simple, with total number $2m$. Then

```math
\operatorname{rank}\!\left(\frac{X_0-X_0^*}{2i}\right)=m.
```

The export is `NLA.MF18.canonical_full_complex_rank`. Its assumptions are
`GreenAssumptions` plus the original uniqueness and root-count premises.
`full_complex_rank` proves the stronger result without uniqueness. The
canonical wrapper keeps that premise so its statement matches the source.
The polynomial determinant, root multiplicities, spectral radius and complex
matrix rank have concrete definitions; no literature theorem is an axiom.
In particular, `regularizedB` uses the displayed **plus** $i\eta D^*$; it is
generally not the adjoint of `regularizedA`.

The proof includes singular $C$ or $D$, $n=1$, $m=0$, simple roots at
$1$ and $-1$, and arbitrary Jordan structure strictly inside the disk.
Existence and nonsingularity of the limit and simplicity of the circle roots
remain original assumptions. A general defective-unit-root extension is not
part of this target. The [retained canonical statement](source-inputs/canonical/README.md)
and [mathematical solution](source-inputs/canonical/solution.md) are pinned to
revision `e7519c46fd249a6a033bfe5d11c66bf47f7f8885`; their historical relative
links are resolved in that original repository tree.

## Proof and evidence navigation

The [proof map](PROOF-REVIEWER-MAP.md) explains the argument and its treatment of
degree drops, algebraic multiplicities and generalized eigenspaces.
[IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json) binds each of C01–C25 to its
source file, line, source hash and exact frozen-header hash, and lists every
source in the proof closure. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records
the small exact LeanCert obligation and its actual use.

The two independent full baseline reviews and their successor approvals are
indexed in [REVIEW-INDEX.md](REVIEW-INDEX.md) and
[REVIEW-INDEX.json](REVIEW-INDEX.json). The baseline request-changes reports
remain immutable. The approved continuation resolves their bounded reuse and
comment requests with 17 edited files, preserving all 25 headers and the three
frozen files. These are AI-agent reviews under pinned Tau Ceti guidance, not
external human peer review or execution of the Tau Ceti service.

The statement-first gate was local288. `Challenge.lean` deliberately contains
25 statement placeholders in its separate environment. The proof closure has
no unresolved `sorry`; the actual final local log reports only `propext`,
`Classical.choice` and `Quot.sound` for all 25 configured theorems, and Solution
requests all 25 kernel-trust checks. Historical comments in the frozen sources
describe their preproof preparation state; they remain byte-identical and do
not replace the current records.

Local341 compares all 25 universe lists and elaborated types after erasing
binder names only. Eight raw type strings differ by generated binder names.
The 193-node actual proof-body graph reaches `certified_half`, both exact
certificate-check declarations, and
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. This diagnostic is
distinct from the final real Comparator run. Exact commands, source origins,
logs and reused-output lineage are in the local340 completion record and
local341 diagnostic packet identified by [INTEGRATION-REQUIREMENTS.json](INTEGRATION-REQUIREMENTS.json).
The documentation author and both reviewers did not rerun Lean.

## Pinned standalone configuration

`lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged copies
from the approved snapshot. The project is `NLAMF18`, with `Solution` as the
default target. Lean is `leanprover/lean4:v4.33.1`; Mathlib is pinned at
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert at
`621a43d7cf21f87872392a01e874f2f1dbddc926`. All transitive revisions are retained
in the Lake manifest. [LAKE-CONFIGURATION.json](LAKE-CONFIGURATION.json) binds
the exact configuration bytes. The original docs task did not run Lean. Root used its serial local runner with `--threads=1 --memory=4096` and authenticated pinned dependencies; the later standalone Linux harness compiled the exact package independently.

From this project directory, `lake build Solution` is the ordinary Lake build target. The final repository check belongs
on the non-root Linux runner. From the repository root, the established harness
entry points are:

```sh
tools/lean/bootstrap.sh /tmp/nla-mf18-tools
tools/lean/verify.sh matrix-functions-and-stability/MF-18/lean /tmp/nla-mf18-tools
```

These reproduce the kind of check actually completed at the immutable proof revision above. They were not run by the source reviewers or original documentation author; exact execution roles and commands remain in the retained receipts. The historical documentation checker, retained in the docs archive, checks schema
and integrity against the campaign evidence; it does not compile. See
[verification/README.md](verification/README.md) for the retained execution records.

## Attribution and public scope

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA, authored the
complete mathematical resolution and is credited for the formalization, with
substantial ChatGPT/Codex assistance. The principal MF18 proof and cleanup agent
was `/root/mf06_final_referee2`; `/root` ran the compiler and coordinates
packaging. `/root/nm04_final_referee1` and `/root/mi24_full_referee1` are nonauthor
proof reviewers. The latter prepared this documentation only after sealing its
source review; this is not independent review of its own metadata.

Guo, Kuo and Lin posed the original question and proved earlier results.
Matthew J. Colbrook's earlier real-coefficient, scalar-regularization auxiliary
theorem, including its defective-root extension, retains its separate credit
and scope. Mathlib and LeanCert authorship and the Yakov Pechersky
determinant-degree adaptation are recorded in [SOURCE-ATTRIBUTION.json](SOURCE-ATTRIBUTION.json).
No bulk primary-paper PDF or extracted paper text is distributed in this draft.

[PUBLIC-SCOPE.json](PUBLIC-SCOPE.json) records the retained 2026-09-18 public
audit: 15 repositories, 269 branch heads and 223 distinct commit trees, followed
by the dated upstream PR search for `MF-18`. That path/ID scan reports no
target-named formalization path. The PR results include the already merged
mathematical solution #116 and the earlier auxiliary contribution #47. This
documentation task made no new network query. The records do not establish
universal novelty or inspect private, deleted, unpublished or differently named
work. The existing mathematical resolution is not counted again.

The [coordinator publication preflight](verification/MF18-ROOT-PACKAGE-PREFLIGHT.json) checks the complete package, current upstream source correspondence, dependency pins and privacy. It preceded the actual Linux execution and is separate from the two independent full mathematical/source reviews.
