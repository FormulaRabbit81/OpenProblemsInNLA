# MI-04 generic assembly after local diagnostic failure

This private candidate is authored by `/root/mi04_independent_referee`, which
cannot referee this repair. It changes one existing proof body and adds one
proved private helper; all 169 pre-existing headers, 21 frozen contracts, ten
frozen files, other twenty sources and all imports/options/trust commands stay
exact. The existing decomposition helper and final matrix theorem body are
unchanged. All new helper statements were recorded in PLAN.md before proof code.

The actual completed local development-02 receipt has 67 available successful
modules, four failures and sixteen blocked dependants. Its MI04 failure is the
default-200000-heartbeat `whnf` timeout in normal_operator_eigenbasis. The
isolated diagnostics-only run also actually failed with that unchanged limit.
It counted 754109 LinearMap.toAddHom, 661105 ContinuousLinearMap.toLinearMap,
259278 DFunLike.coe and 42610 CVector unfoldings. This supports moving the same
coercion and reconstruction proof to an abstract inner-product space. Counters
do not identify a particular tactic and do not measure this candidate's speed.
The downstream unknown constant and trust rejection are failure evidence,
never an accepted certificate. This evidence is local macOS execution, not a
new GitHub run or Comparator execution.

The selected minimal factoring adds only normal_eigenbasis_of_joint_solver:
the old assembly argument is parametrized by an abstract space/index type and
an explicitly supplied commuting-symmetric joint-eigenbasis solver. It obtains
the actual normal operator's real/imaginary parts from the existing proved
helper, transports commutation to linear maps, calls the supplied solver, and
reconstructs z_i=alpha_i+I*beta_i pointwise. The old matrix-space theorem now
supplies the already proved commuting_symmetric_eigenbasis to that helper.
No additional assumption reaches an existing theorem. Zero dimension, repeated
eigenvalues, singular operators and arbitrary complex normal inputs are retained.
The two smaller optional generic helpers in the recorded plan are unnecessary
for this first minimal candidate and have not been introduced.

All arithmetic and the genuinely consumed fixed LeanCert certificate stay
unchanged. The new helper and specialized theorem retain default200000; the
previous JointBasis scope is untouched. No resource, import or trust relaxation
is included. Root owns the only compiler process; this script executes none.
Independent nonauthor review and an actual compile are pending. No proof,
performance, canonical acceptance, publication or count change is claimed.

A first pre-write bookkeeping guard expected Challenge in the local source-only
assembly, which intentionally contains proof modules rather than Challenge
copies. It stopped before any packet output or source change. The corrected
guard checks the unchanged Challenge in the development worktree and literal
a6ff Git tree against the same frozen bytes; the stopped script is retained.
