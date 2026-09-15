# IE-18: prior negative resolution and attribution correction

**15 September 2026. PASS: the cited prior work disproves the same canonical target.** Oliver Krzysik brought the missing reference to the maintainer's attention. The coordinating reviewer and a separate Codex agent independently checked the source correspondence and exact examples. This is informal source and arithmetic review, not external human peer review.

## Prior source and exact target

Yunhui He, *The worst-case root-convergence factor of GMRES(1)*, [arXiv:2501.10248v1](https://arxiv.org/abs/2501.10248v1), was submitted on **17 January 2025**. Despite its title, Section 2.3 also treats restarted Anderson acceleration. Equation **(2.36), p. 14**, states the four-step identity, and **Example 2.1, p. 15**, explicitly gives three counterexamples. [Versioned PDF, counterexample page](https://arxiv.org/pdf/2501.10248v1#page=15).

He uses the same system matrix A=I-M, the same scalar coefficient, and Psi(v)=R(v). His Upsilon(v)v is R(R(v)). Substitution of a_i=1-m_i makes his Lambda* exactly the squared eigenvalue-pair expression in IE-18. This is [Krzysik, De Sterck and Smith, Conjecture 10, equation (27)](https://arxiv.org/html/2312.04776v4), not ordinary GMRES(1)'s residual map. He explicitly distinguishes finite-step amplification from the asymptotic root-convergence question immediately after the examples; the latter is not resolved by them.

## Exact recomputation

For the first prior example, A=diag(1,2,3), M=diag(0,-1,-2), v=(15,5,1), the canonical map gives

```math
R(R(v))=\frac{(0,-462500,684500)^T}{646123},\qquad
\frac{\|R(R(v))\|_2^2}{\|v\|_2^2}
=\frac{682446500000}{104786207713379}>\frac1{256}.
```

The proposed norm amplification is 1/16, so this strict squared comparison disproves the identity. Symmetry, nonzero M and exclusion of one from its spectrum all hold. The other two prior examples also pass exact recomputation. A few intermediate fractions and numerical approximations printed in Example 2.1 have typographical/arithmetic errors; the checks here derive the residuals directly from its stated matrices and vectors and confirm all three strict violations.

Run the standard-library-only checker from the repository root:

```sh
python3 references/colbrook-recovered-2026-09-11/verification/check_ie18_prior_work.py
```

[Exact results](IE-18-prior-work-exact-results.json) include all three prior examples and Colbrook's later formalized example. No floating-point optimization or numerical inequality is used.

## Repository disposition

Credit **He (2025)** for the prior negative resolution. The September 8 and 10 literature searches missed this paper and are now explicitly identified as corrected historical records. Colbrook's September 2026 positive-definite-contraction examples and unbounded-underestimation argument remain as supplementary results, without a first-discovery claim. Stepaniants's later Lean proof still verifies Colbrook's specific example and the full negative identity; it does not certify historical priority or the parameter-family result.

The original IE-18 statement, permanent ID and canonical path are retained, and its **Lean verified** status and catalogue counts do not change. The manuscript URL circulated by the maintainer now opens with the prior-work notice. Its complete reviewed body and original source under `submitted/` remain unchanged. Frozen Lean proof, metadata, review and execution records remain unchanged; its current README adds the attribution correction.

The package's original `record-sha256.json` remains a dated historical manifest. The [separate correction manifest](IE-18-attribution-update-2026-09-15.json) binds the updated publication files and retained sources, so the older export hashes are not silently rewritten.
