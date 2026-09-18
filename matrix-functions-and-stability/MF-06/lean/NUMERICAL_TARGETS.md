# MF-06 numerical obligations before any new Lean source

Author/contributor: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance. The original target is attributed to Epperlein and Wirth; extremal-norm and nonresonance background retains its cited authorship.

Stage: numerical and semantic target sheet written before the statement-only Lean draft. No proof body, statement approval, freeze, Lean elaboration, MF-06 LeanCert execution or Comparator run is claimed.

## Full numerical target

For every integer d>=1 and every fixed nonempty compact M of complex d-by-d matrices, choose r,C>0 before introducing N. Every nonempty compact N in the same dimension with delta=d_H(M,N)<r must satisfy

    rho(N) >= rho(M) - C*delta.

Here d_H is the original max of the two sup-inf expressions in the actual spectral operator norm, and rho is the actual all-word root limit. Existing MF05/MF07 concrete definitions and proved full semantics are the intended reuse boundary. The perturbed family must not be required to preserve any invariant subspace of M. There is no finite-generator, irreducibility, product-boundedness or positive-radius hypothesis on the final target.

## N0: genuinely consumed kernel numerical certificate

The existing MF05 `half_radius_certificate` establishes 0<1/2 and 1/2<1 using `interval_decide (trust := kernel)`. Reuse that exact source-bound theorem, once its published source pin is available, to certify the positive lower trajectory factor and a strict neighborhood shrink. A new duplicate half-radius lemma is unnecessary. This consumption must occur in the actual cone/trajectory proof, not merely in an unused import or a metadata claim.

No new transcendental numerical enclosures, finite-dimensional matrix search, interval subdivisions or floating-point premise are needed. Dimensions, words and limits stay symbolic. The following inequalities are algebraic proof obligations, not empirical tests.

## N1: cone invariance and a uniformly positive growth factor

For real q,K with 0<=q<1 and K>=0, put

    H=(K+1)/(1-q), L=H+1.

Prove H>=1, L>=2 and q*H+K=H-1. For 0<=t<=1/L^2, prove

    H-1+L*t <= H*(1-L*t),
    1/2 <= 1-L*t.

The exact difference in the first inequality is -1+L^2*t. The consumed N0 certificate makes the second lower bound strictly positive. Thus a cone trajectory with a<=H*b and b>0 remains in the cone and retains quotient norm at least (1-L*t)^n for every n. The admissible perturbation size t=c0*delta uses one fixed c0>0 supplied by genuine finite-dimensional block norm equivalence.

## N2: nonresonance sum without square-root evaluation

For n>=1, x_i>=0, K,F>=0, 0<q<1, assume x_i<=K and x_i*x_j<=F*q^abs(i-j) for i!=j. The source proves

    sum x_i <= K + sqrt(K^2 + 4*F*q/(1-q)^2).

Only a finite bound independent of n is used. It suffices, with G=F*q/(1-q)^2, to prove the simpler bound

    sum x_i <= 2*K + 4*G + 1.

The prefix-half argument gives X^2/4-K*X/2<=G. For X>2*K+4*G+1, X>=1 and X-2*K>4*G+1 contradict X*(X-2*K)<=4*G. This alternative eliminates square roots while preserving the complete target; it changes only an unspecified internal constant. Keep the source's hypotheses n>=1, K,F>=0, and cover the empty intervening word in the paired-product application.

## N3: geometric cross-cut estimate

For every finite cut, prove

    sum_{i<=h<j} q^(j-i) <= q/(1-q)^2,    0<q<1.

Use finite geometric sums or existing convergent-series bounds. No enumeration over word length or interval bound on q is permissible: q is an arbitrary real in (0,1).

## N4: exterior representation bounds may have fixed dimensional constants

For an actual k-th compound matrix E_k(A), 1<=k<=d, it is sufficient to prove fixed positive constants D(d,k) and T(d,k,L) such that

    ||E_k(P)||_2 <= D(d,k)*||P||_2^k,
    ||E_k(A)-E_k(B)||_2 <= T(d,k,L)*||A-B||_2

when ||A||_2,||B||_2<=L and L>0. The first constant is outside the power of the word length, so it disappears under nth roots. This gives the exact necessary rho(E_k(N))<=rho(N)^k. The second constant supplies a local image-Hausdorff bound. The source's sharper constants 1 and k*L^(k-1) are not part of the canonical target.

A concrete conservative choice is D(d,k)=N*k! and T(d,k,L)=N*k*k!*L^(k-1), where N=choose(d,k). Each sorted minor is a sum of k! products; the difference of two products has k telescoping terms; and the spectral norm of an N-by-N matrix is at most N times its maximum entry magnitude. These constants are symbolic and must never be computed by enumerating permutations or dimensions. The determinant formula and finite-product estimates should be proved algebraically.

For paired tensor products of matrices of positive sizes m,n, the elementary entry bound also gives both inequalities

    ||A tensor B||_2 <= m*n*||A||_2*||B||_2,
    ||A||_2*||B||_2 <= m*n*||A tensor B||_2.

The second follows by choosing maximum-magnitude entries of A and B and comparing their tensor entry to the operator norm. Iteration gives fixed dimension-only constants. These suffice for every paired-radius comparison: they enlarge word-independent constants but do not alter decay exponents. Exact Hilbert tensor norm multiplicativity need not be formalized.

The compound matrix must be the concrete matrix of `exteriorPower.map` in the exterior basis, or equivalently its sorted-minor matrix, and must satisfy E_k(PQ)=E_k(P)E_k(Q). Arbitrary replacement functions satisfying assumed norm properties are prohibited.

## N5: avoid a final fractional-power proof

For every integer k>=1, u>=0 and 0<=z<=1, if z<=u^k, then z<=u. Split u>=1 (immediate) and u<=1 (then u^k<=u). With z=1-C1*delta, this returns the linear lower bound from the exterior radius inequality without evaluating or differentiating a kth root. Shrink the neighborhood to C1*delta<=1/2 if needed, consuming N0.

## N6: normalization and zero radius

If rho(M)=0, nonnegativity proves the target for any r,C>0. For R=rho(M)>0, prove the exact positive-homothety identities

    rho(R^-1 M)=R^-1*rho(M),
    d_H(R^-1 M,R^-1 N)=R^-1*d_H(M,N).

After applying the normalized theorem, choose r=R*r_normalized and multiply the conclusion by R. No division by a zero radius, no conditioning on the nearby radius being positive, and no hidden restriction on N is allowed.

## Statement-draft choices fixed before writing the Lean files

The independent Challenge will expose the complete final target, the actual sup-inf and root-limit correspondences, and the substantial source prerequisites as conclusions to prove. It will not assume any compact-family extremal norm, invariant flag, stable-kernel theorem, exterior representation, product boundedness of an arbitrary reference, or target perturbation theorem.

The concrete exterior matrix is its sorted-minor matrix. A separate exact coordinate contract identifies it with the pinned algebraic `exteriorPower.map` and standard exterior basis. This is equivalent to the pre-code abstract-map definition and eliminates a new complex exterior inner-product development. The constant N is literally the cardinality of the k-subset basis, with a separate equality to choose(d,k).

A block labeling b:Fin d -> Fin r partitions the actual coordinates. The block dimensions are the cardinalities of its fibers; each diagonal matrix is the corresponding actual submatrix. Upper triangularity uses the order on the labels. The invariant-flag theorem must produce a surjective labeling and an actual inverse pair of change-of-basis matrices. Labels need not occupy contiguous coordinates; a permutation groups them, with no mathematical loss.

An allocation is a function a_i in Fin(d_i+1), so every degree is between zero and the actual block dimension. Its matrix is the literal product of entries of the actual compound diagonal-block matrices, reindexed through a finite equivalence. Every factor uses the same original generator A. All degree-zero factors, empty words, vanishing minors and zero matrices are retained.

The key paired-allocation estimate is symbolic. For distinct allocations a,b of the same degree k, max(a,b) has degree greater than k and min(a,b) degree less than k. A fixed finite constant bounds the norm of the paired allocation tensor by the product of the max/min allocation norms. This only permutes scalar norm factors, uses finite entrywise tensor bounds, and never divides by a possibly zero factor. No singular-value computation is required.

The scalar separated-sum bound is stated for every n, including n=0, which is immediate; the nonempty source argument is unchanged. Every substantive matrix-family radius contract keeps nonempty compact families and positive ambient dimension when necessary for the reused root-limit semantics.

### Planned independent contracts

C01 reused kernel half-radius certificate; C02 reused full canonical Hausdorff semantics; C03 reused arbitrary-radius root-limit semantics; C04 reused positive radius scaling; C05 genuine bounded-envelope norm; C06 actual tail-envelope convergence to a continuous complex seminorm; C07 attained max recurrence for that seminorm; C08 actual proper invariant stable kernel and exponential restricted growth; C09 cone algebra and half-factor positivity; C10 normalized product-bounded-reference lower Lipschitz; C11 all-length scalar separated-sum estimate; C12 actual finite-block radius formula; C13 paired block nonresonance gives product boundedness; C14 irreducible radius-one product boundedness; C15 actual irreducible invariant flag; C16 similarity preservation; C17 compound dimensions; C18 exact exterior-coordinate correspondence; C19 compound algebra; C20 compound norm-power bound; C21 compound local Lipschitz; C22 paired tensor algebra; C23 tensor norm comparisons; C24 allocation dimensions and degree bounds; C25 allocation algebra for upper-triangular matrices; C26 allocation product boundedness; C27 actual compound-allocation radius formula; C28 distinct allocation max/min degrees; C29 paired allocation norm bridge; C30 critical allocation nonresonance; C31 compound product boundedness from full allocation nonresonance; C32 compound compact-image and radius-power semantics; C33 full critical compound existence and product boundedness; C34 actual compound image-Hausdorff bound; C35 positive Hausdorff scaling; C36 root-free final scalar transfer; C37 normalized unrestricted-reference lower Lipschitz; C38 complete canonical lower Lipschitz, including radius zero.

All C05-C38 are currently obligations, not completed proofs. C01-C04 are existing source-bound published results selected for exact reuse. Formal MF-06 consumption is pending. The two independent statement reviews must inspect the actual Definitions and Challenge and may request corrections before freezing.
