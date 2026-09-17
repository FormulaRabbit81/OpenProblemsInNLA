# Reciprocal contracts 25/26 — author evidence closure

The three authored modules have actual root-run local success on their exact current bytes. This is an **author handoff, not an independent proof review**. The author is `/root/sf_ra_runtime_referee`; subsequent independent reviews must treat these three sources as authored work.

| Module | Source SHA-256 | Actual origin |
|---|---|---|
| RootProductReflection | `7609e8e5b570e29aca1ffed68333ba80a13c019237f4ebd512bad97144ce3721` | 108, 13.44 seconds |
| ReciprocalRoots | `6697dbd9e5a1c90cb114e83a7ed6a2434fa7116feee112774e83275ec97e17a6` | 111, 21.03 seconds |
| InsideFactor | `8933c7f29d06f2dd4d1a9b3cba7d656acc0e8ef558f578ac5b368d3e5f2a19b5` | 111, 5.72 seconds |

The shared helper reflects the exact product of a full multiset of nonzero roots at its cardinality. Contract 25 obtains reciprocal pairing through complete complex factorization and the library multiset roots API, then uses multiset filters to retain every multiplicity. Contract 26 reuses that partition and the same reflection identity. Its scalar is the nonzero complex value `leadingCoeff / D`, with `D` the product of the negatives of conjugated inside roots. It makes no positivity claim. Empty multisets and `ell=0` remain included. Direct Mathlib monicity, degree, roots and finite-product APIs are used throughout.

Both public headers match the immutable frozen statements exactly. All thirteen frozen files remain unchanged. The full project dependency closure is five sources: Definitions, Reflection, and the three new modules. No other current proof source was altered. The accepted pre-code plan, authorization, original candidates and repair are retained in handoffs 01–04 and rehashed here.

Actual 110 failed at `filter_map`'s explicit function-composition wrapper, producing `sorryAx` and a trust rejection. That failed source, full raw log and finalized receipt remain retained in handoff 04. The sole repair added `simp only [Function.comp_def]`; no statement, hypothesis or resource setting changed. Actual 111 then passed both exact contracts. All three selected successful raw logs were read in full and contain exactly `propext`, `Classical.choice` and `Quot.sound`, with no warnings. Sources contain kernel-trust assertions.

Run 111 as a whole was mixed: `NLA.SP15.ShiftedDeterminant` failed separately. That module and all other selected projects/modules are outside this handoff. No whole-run pass is claimed. Commands, receipts, assemblies, source files, current output hashes and dependency output hashes are bound by `AUTHOR-EVIDENCE.json` and `BINDINGS.json`; compiled outputs are not copied. The reused dependency checks cover exact current sources/outputs, their full project source closure and immediate prior receipt rows, not every historical reuse hop.

The collector and `verify.py --sources` were actually executed. The collector performed 130 source/evidence checks. The author did not run Lean, mutate caches, change compiler settings, use Git/network, or claim a new kernel replay. Root owns all actual serial compiler runs: one process, one thread, 4096 MiB. No new interval computation was added. Whole-target independent proof reviews and non-root Linux Comparator/kernel/sandbox checks remain pending. Count change: zero.

Preserve George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Codex assistance and prior mathematical/library attribution. No email is included in this note. Verification commands check packet hashes only; this author packet does not replace independent source review.
