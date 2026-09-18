# Numerical statements before proof

There is no finite-dimensional matrix data set, matrix-entry interval box, truncation in dimension, or numerical grid in the exponent `p`. The target is symbolic for every positive dimension, arbitrary complex positive definite inputs and all real `p≥1`, plus infinity.

The only planned LeanCert statement is C01:

\[
\forall u\in[0,1/2],\quad 1/2\le1-u\le1.
\]

All numbers are exact dyadic rationals. One affine expression on one box is sufficient; no subdivision or high-precision arithmetic is mathematically needed. The implementation should select `leancert.trust = kernel` and use a checked LeanCert tactic/proof, following the source-pinned MF05 half-certificate pattern. No tactic has been run and no precision success is claimed here.

The proposed consumer is C09. First prove symbolically from `p≥1` that `u=1/(2p)` lies in `(0,1/2]`. The certificate's lower bound then supplies nonnegativity of `1-u` in the actual scalar weighted AM–GM calls for the two spectral bases. This consumption must remain in the proof term and eventually be confirmed by theorem-body constant inspection. A certificate merely imported or printed, with no path into the final theorem, does not satisfy the plan.

All remaining constants and exponent bounds, including `r=1/(2p-1)∈(0,1]`, the Furuta extension parameter and the positive normalizing norms, are symbolic real-algebra arguments. All denominators are discharged from explicit positivity. Real powers and the matrix functional calculus are never approximated by floating-point values.

The old September 15 notes are retained as history. Their proposed Linux-first statement typecheck is superseded by the current local-development/GitHub-final-check workflow. This preparer is not authorized to run a compiler; the parent may elaborate the draft statement environment locally under the campaign's single-compiler limits before the independent reviews and freeze.
