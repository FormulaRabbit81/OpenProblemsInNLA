# SF-01 observed local repair — independent source continuation

**Approve the exact one-body repair for root-coordinated compilation.**
Reviewer `/root/mi04_independent_referee` is a nonauthor of this repair and of
the problem's proof. I read the complete before/after module, entire actual
failure log, precise patch, plan and relevant pinned primary APIs. This extends
my preceding full-prefix source review without claiming complete verification.

The observed SF01 error is an unreduced matrix-entry goal in ridgeEval_apply.
The repair substitutes Matrix.add_apply and Matrix.smul_apply for the unused
Pi variants. Both pinned Matrix lemmas are literal entrywise definitional
equalities (Matrix/Defs298–303); Matrix.sum_apply (Data/Matrix/Basic71–73)
then exposes each weighted term. The scalar ridge formula and every hypothesis
are unchanged. The separate vector-action helper correctly retains Pi lemmas
after converting matrix action to vector action. All six module headers,
other twenty-four selected sources and the prior fourteen source-level public
implementations are preserved. The three later ridge modules were blocked in
that actual run; approval of this edit does not assert that they compile.

The audit rehashes the complete 25-source selected closure, immutable
replacement path, unchanged nine frozen files and all 24 contracts.
All selected actual predecessor inputs match the terminal local development02
receipt; the full retained log equals the actual log bytes and command hash.
The actual command was root's serial macOS Lean run with the4096MiB cap. It
failed. This is not a new GitHub/Comparator run and does not imply every other
component failed. Primary Mathlib files are checked against literal pinned
commit0df444a360eaa60ab8c11dca51a86af692955474. All imports, trust checks,
numerical obligations, prior source paths and resource settings remain exact.

No statement narrowing, vacuity, assumed target or new numerical computation
appears. Original mathematical credit, formalizer's name/department/university,
AI assistance and license remain. No new email is introduced. This reviewer
ran no Lean/Lake/cache process, edited no source/worktree/Git, and changed no
publication or accepted count. Actual compilation remains pending; full final
source review, Linux kernel/Comparator/controls and exact-publication checks
remain separate gates.
