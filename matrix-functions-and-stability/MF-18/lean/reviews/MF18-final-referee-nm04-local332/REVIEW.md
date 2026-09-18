# MF-18 independent full-source review — exact local332

**Mathematical source verdict: approve. Overall code verdict: request changes.**
No semantic defect or weakening of the original target was found. The three
requests in `VERDICT.json` concern reuse, duplicate algebraic proof code and
undocumented definitional bridges. Approval is bound to the exact source hashes
in `SCOPE.json`; this is not final publication or Linux acceptance.

I am Codex agent `/root/nm04_final_referee1`. I have never authored MF-18 proof
code. I previously independently reviewed its statements; that does not make me
a proof author. I have not edited a candidate source, invoked Lean/Lake or
Comparator, run a GitHub job, or read another final referee's verdict before
recording these conclusions. The only executed verifier for this review is the
read-only Python evidence checker included in this packet.

## Whole-target alignment

I read the unchanged canonical README/problem statement, the complete canonical
solution, all transparent definitions, all 25 frozen contracts, the author source
map, and every file in the full 38-module import closure including Solution.
`Mat n` is the ordinary complex matrix type, `hermitianImaginaryPart` is literally
`(2i)^-1 (X-X*)`, and matrix rank is the standard Mathlib rank. The polynomial is
the actual determinant of `lambda^2 C* - lambda R + C`; all counts are multisets
of polynomial roots with algebraic multiplicity. The finite nonsingular limit
and simple unit-circle roots remain original assumptions, not conclusions
silently imposed as new hypotheses.

`GreenAssumptions` contains precisely Hermitian R/P, circle positivity, the
nonsingular stabilizing family, the right-sided limit, nonsingular X0, regularity
and simple unit-circle roots. It contains no rank, count-selection, Stein
identity, or stabilizing-limit conclusion. The C02 semantics bridge identifies
all characteristic roots strictly inside the unit disk with the original
spectral-radius premise, for every positive dimension. C24 proves the stronger
statement without uniqueness; C25 retains the original uniqueness hypothesis
verbatim. Leaving that deliberately unused original hypothesis is appropriate,
and I do not request a change to the frozen signature.

The proof retains arbitrary complex C and D, including singular matrices;
`regularizedB` is correctly `C*+i eta D*`, not the adjoint of `regularizedA`.
I explicitly challenged zero/root-degree degeneracies, unit roots at +1 and -1,
m=0, arbitrary stable Jordan blocks, the right-sided filter, and the possibility
that the limiting imaginary part is indefinite. No excluded original case or
hidden positivity/diagonalizability premise was found.

## Mathematical dependencies checked

1. **Regularized root count.** Positive averaging gives P positive definite,
   and evaluating circle positivity at the negative circle point gives the
   sign needed by the homotopy. The homotopy boundary matrix is an invertible
   scalar multiple of Hermitian H plus i eta times positive K, including both
   endpoints. At t=0 its scalar determinant is a nonzero constant times X^n.
   No invertibility of C, D or a polynomial leading coefficient is used.
2. **Homotopy without assumed root continuity.** The fixed-grade Cayley
   transform uses p(1), which is nonzero by boundary nonvanishing, to obtain a
   genuinely monic degree-N polynomial. A degree drop contributes roots at -1,
   outside the counted right half-plane. The exact root-product factorization
   proves the count correspondence with multiplicities. Coefficient convergence
   uniformly bounds all root tuples by Cauchy's bound; a compact subsequence
   identifies the entire limiting product. No continuous labeling or simple
   interior spectrum is assumed. Eventual sign constancy away from the imaginary
   axis and connectedness give the homotopy count. This also covers N=0.
3. **Complement and limit.** The nonlinear equation gives the exact
   determinant factorization. The n stable characteristic roots exhaust the
   regularized disk count, so the complementary factor has no closed-disk root.
   Reciprocal evaluation gives strict stability of the complementary matrix.
   Along eta_k=1/(k+1), inverse continuity at nonsingular X0 passes the equation
   and both spectral bounds to the limit. Weak stability is proved from a full
   characteristic-product lower bound outside the disk, rather than assumed
   continuity of spectral radius. The complementary value at zero is explicitly
   nonzero even for singular B.
4. **Reciprocal count.** Fixed-grade reflection of the determinant is its
   coefficient conjugation. Reflecting each root factor accounts separately for
   original zero roots and the lost leading degree. It yields
   degree(p)+multiplicity_0(p)=2n and 2 diskCount(p)+circleCount(p)=2n. The selected
   factorization transfers the complete disk count, and simplicity is inherited
   only at actual unit roots. The argument does not pretend degree(p)=2n.
5. **Stein equation and nonzero unit pairing.** All adjoints and product orders
   in H=S*HS are correct. The implemented alternative to the manuscript's
   adjugate derivative proof is valid: a simple pencil root forces the other
   determinant factor to be nonzero and the characteristic root to be simple.
   The unit-circle pencil is a nonzero scalar times a Hermitian matrix. Its
   right kernel therefore yields the required left eigenfunctional. That
   functional is nonzero because its coefficient matrix is invertible. A
   nonzero left eigenfunctional at a simple characteristic root cannot vanish
   on its right eigenvector, by the complete primary decomposition. Finally its
   value is conjugate(v*Xv)-v*Xv, so the H pairing is nonzero. This handles n=1
   and the unit points +1/-1 without angular parametrization or derivatives.
6. **Full Jordan and rank arguments.** The generalized Stein identity is proved
   by double induction on both annihilating powers. Nonresonance with a strictly
   stable eigenvalue follows from the other eigenvalue's weak stability. The
   full generalized eigenspace decomposition then places the entire stable
   subspace in the kernel, without bounded-power or semisimplicity assumptions
   on the interior. Its dimension equals the complete interior multiplicity.
   Distinct selected unit roots give a diagonal pairing with nonzero diagonal,
   hence independent images in range H and the lower bound. Rank-nullity gives
   the matching upper bound. Empty unit spectrum gives rank 0 as required.

## Code and library review

The pinned Tau Ceti correctness, generality, proof-quality, attribution and reuse
rubrics were read and applied within this standalone project scope. Their use is
not a claim to have run the Tau Ceti service. Search records cover all 150 new
source declaration names plus the substantive polynomial, spectral, generalized
space and Hermitian families in the pinned Mathlib. No TauCeti mathematical
checkout was available in the retained source scope; I make no exhaustive
semantic search claim for it. The only same-name hits were unrelated generic
`pairing` uses.

**R1:** The two local Hermitian-sum proofs can directly reuse the located
`Matrix.isHermitian_add_transpose_self` at the scalar-multiple matrix. Its pinned
source is bound in the packet. This is a local code request, not a mathematical
failure.

**R2:** The regularized and unregularized matrix-factorization proofs repeat
one algebraic identity. Factor it with arbitrary A,B,Q,X and the equation
X+B X^-1 A=Q, then specialize both existing declarations. The present results
are true; this avoids duplicate proof code and unnecessary dependence of the
core identity on a stabilizing-family wrapper.

**Q1:** `BRIDGE-INVENTORY.json` records all 32 change/show sites. One existing
IsRoot explanation in SelectedCount is adequate. The other 31 need either an
explicit rewrite or a nearby explanation of the exact wrapper/coercion bridge;
two overlap R1 and can disappear with reuse. No wider proof redesign, changed
mathematical statement or rewritten frozen file is requested.

The matrix degree estimate identifies its adaptation of Mathlib's existing
linear-entry determinant proof. LeanCert's accepted MF05 pattern and its
separate Colbrook mathematical provenance are credited. Guo--Kuo--Lin retain
original-problem/prior-result credit, George receives the complete-complex proof
credit, and the earlier real auxiliary result is not used as a surrogate target.
The source identifies George's department and Caltech affiliation and publishes
no email. Final package licensing/links, public-branch status and publication
privacy remain separate gates.

## Evidence and limitations

I read the actual local332 capture script without running its write-producing
capture function, inspected every fresh-origin log for the 38 retained sources,
and read the local334 diagnostic source and comparison logic. The source-bound
receipt histories distinguish fresh executions from exact reused outputs.
All25 final axioms reports contain only `propext`, `Classical.choice` and
`Quot.sound`; Solution requests all 25 corresponding kernel-trust assertions.
Several old origin logs contain harmless lint suggestions and unused original
hypotheses. I do not describe those logs as warning-free.

The statement diagnostic independently elaborates the frozen Challenge and
Solution and removes only binder names. All25 normalized types and universe
lists match. The differing raw dump hashes are consistent with binder-name
variation, not a blanket claim of raw byte identity. The actual body graph
reaches `certified_half` and the LeanCert checked bound from the canonical final
theorem. The numerical calculation is only the constant half-interval statement,
used by positive averaging; it is not a decorative unconsumed certificate.

The included read-only verifier rechecks immutable hashes, the complete source
and import boundary, literal frozen headers, source-matched execution origins,
logs and axioms, both diagnostic dumps and the recorded body edges. Its success
is evidence-integrity verification, not a new Lean execution or an independent
Linux kernel replay. The root executed the actual local Lean runs. There is no
MF18 Linux Comparator/default-kernel/sandbox acceptance yet in this scope.
No completed-count increment or authorization to label a final published commit
verified is issued by this packet. A narrow successor review after the requested
cleanup and successful root compilation can close these code findings.
