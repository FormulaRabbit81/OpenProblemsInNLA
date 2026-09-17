# SF-01 independent mathematical preflight

Reviewer: `/root/mi04_independent_referee`, a nonimplementing agent distinct from the route author `/root/ie13_continuation` and the first reader `/root`.

**Verdict: approve this finite route for drafting the complete Definitions and Challenge.** I found no mathematical blocker or restriction of the original target. This is a feasibility review, not approval of unwritten Lean statements or proofs, compilation, Comparator, a formalization count, or publication. No author source was edited and no Lean/Lake program was run.

I read the complete canonical README, complete Colbrook manuscript, FINITE-ROUTE.md, OBLIGATIONS.md and REPORT.md. The target and manuscript exactly match literal upstream commit `ce47b5630bf3680d9211131c3a43825b022c139a`; their Git blob and SHA-256 identities are independently checked. All 35 feasibility inventory bindings and all 14 retained primary/reuse source bindings were rehashed against their literal Git objects. CHECKS.json distinguishes the new API ranges actually read from mere complete-file hash authentication. This review does not repeat or independently extend the public duplicate search.

## Full-target fidelity

The input remains every real n by n matrix, n >= 1, whose comparison matrix is `sI-B` for entrywise nonnegative B and s strictly greater than B's **complex** spectral radius, together with positive diagonal. The required recurrence is exactly X_0=A and X_(k+1)=(X_k+X_k^-1 A)/2 for every natural k. There is no normality, symmetry, irreducibility, diagonalizability, input-entry positivity, bounded dimension, or bounded iteration hypothesis. Positive weighted dominance is derived from the original predicate and then converted back for the output; it must not replace either spectral definition by assumption. Every iterate's actual unitness is also required, preventing a totalized singular inverse from satisfying a surrogate recurrence.

The proposed internal rational invariant uses a>0 and b>0 only after the exact first step X_1=(A+I)/2. The k=0 conclusion is the given hypothesis, and A's unitness justifies the first step. Thus this internal restriction does not discard any canonical input. The manuscript's scaled/affine-initialized Newton and Halley extensions are outside the canonical original question and outside this proposed formalization; no extension verification is claimed.

## Spectral and comparison foundations

For C=sI-B, s>rho(B) implies s>0 because the complex spectrum is nonempty in positive dimension. Every C_t=sI-tB on [0,1] is invertible: a kernel at t>0 would give the complex eigenvalue s/t of B, whose modulus is at least s. The t=0 matrix is sI. Continuous inversion on this path and a finite minimum make m(t)=min_i (C_t^-1 1)_i continuous. If m ever becomes nonpositive, an intermediate zero occurs; at that point all coordinates are nonnegative and one is zero. Its equation C_t w=1 has nonpositive left side, a contradiction. This yields v=C^-1 1>0 and Cv=1 without assuming inverse positivity in advance. The real/complex determinant and spectrum transports and continuity away from zero determinants remain explicit proof obligations.

Conversely, for a Z-matrix with v>0 and Cv>0, every diagonal is positive. Choose s=max_i C_ii+1 and B=sI-C>=0. With delta=min_i (Cv)_i/v_i>0, a complex eigenvector's largest weighted coordinate gives |lambda| <= (Bv)_i/v_i <= s-delta < s. The finite complex spectrum converts this uniform estimate to rho(B)<s. All extrema are over nonempty finite sets because n>=1; complex eigenvectors, not just real eigenvalues, are essential.

For t>=0, weighted strict dominance proves A+tI is a unit, and the Z-matrix maximum principle proves C+tI is a unit with nonnegative inverse. The coordinatewise reverse triangle inequality `(C+tI)|y| <= |(A+tI)y|`, applied to each inverse column, then yields resolvent domination by the maximum principle. This includes t=0. Reusing IV03's explicit maximum principle is valid only with its hypotheses proved; its IsInverseM definition does not itself establish the spectral predicate equivalence.

For finite rational data, rewrite each ridge A(A+tI)^-1 as I-t(A+tI)^-1. The comparison resolvent bounds give positive diagonal and the correct absolute off-diagonal bounds for f(A) relative to f(C). Since `f(C)v=a v+b 1+sum w_j (C+t_j I)^-1 1>0`, this yields the original spectral H predicate and actual unitness of f(A). The preserver is available before invoking the Newton inverse.

## Rank-one reciprocal closure and exact matrix order

P=diag(0,t_j)+uu^T/b is positive definite: a nonzero tail coordinate gives a strictly positive diagonal term; if the tail vanishes, u_0=sqrt(a)>0 makes the rank-one term strictly positive. This includes an empty pole family and every zero-weight case. The real spectral theorem gives an orthogonal Q and positive actual eigenvalues lambda, with no distinctness condition. From P e_0=(sqrt(a)/b)u one gets P^-1 u=(b/sqrt(a))e_0 and hence sum d_l^2/lambda_l=b. Therefore every new residue d_l^2/(b^2 lambda_l) is nonnegative; no division by a weight occurs.

The block calculation is substantive, but its proposed identity and unit premises are correct. K has diagonal blocks A and A+t_j I. F=bI+V K^-1 U equals f(A)A^-1. The Woodbury secondary matrix S=K+UV/b is orthogonally similar in the pole factor to the block diagonal family A+lambda_l I, so S is a unit for all original inputs. The pinned `Matrix.add_mul_mul_inv_eq_sub` explicitly requires these units. Woodbury gives `F^-1=(1/b)I-(1/b^2)sum d_l^2(A+lambda_l I)^-1`; the normalization rewrites this as the claimed ridge sum. Finally `(f(A)A^-1)^-1=A f(A)^-1=f(A)^-1 A`, using derived unitness and commutation. Merely quoting the scalar identity would not suffice; the proposed obligations correctly require all these finite block, inverse, conjugation and commutation identities.

Positive halving and concatenation preserve the finite data invariant, so ordinary induction proves every k. The route covers n=1, k=0 and k=1, empty families, zero weights, repeated poles/eigenvalues and reducible/nonnormal real matrices. It needs no numerical eigenvalue computation, eigenvalue separation or truncation in k.

## Conditions for later approval

The statement draft must preserve all thirteen obligation groups, especially the complex finite-spectrum maximum, both spectral/weight bridges, t=0 resolvents, genuine unitness and exact multiplication order. Independent statement review and actual Linux elaboration must precede freezing and implementation. The finite algebra can use generic index types and opaque proved helpers to avoid repeated spectral-witness reduction, without a resource or speedup claim before measurement.

A consumed LeanCert kernel certificate for exact positivity of 1/2 is sufficient for the only proposed numerical obligation; all parameter inequalities remain symbolic. This preflight contains no new certificate execution. Later complete proof acceptance still requires source review, the independently frozen complete target, all-contract Comparator, default-kernel replay, genuine rejection controls and authenticated publication-commit reruns.

Mathematical authorship remains Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Any copied/adapted IV03 formalization must preserve Sidney Holden's attribution and Apache-2.0 license. George Stepaniants may receive the new formalization/integration credit, Department of Computing and Mathematical Sciences, California Institute of Technology, with AI assistance disclosed. The raw manuscript is private source evidence; this review contains no contact address and does not authorize publishing that private archive wholesale.
