# RA-10 Equation (7) scalar step: independent pre-implementation review

**Reviewer:** `/root`, independently of the contract author. **Disposition:** approve the exact public signature in `RIDGE_COMPRESSION_EQ7_SCALAR_PRE_REVIEW.md` at SHA-256 `a6ecfddc941025db12409457c9b04792eb5c4cf919b5c44041b0f8b250dd194c`. It is a scalar dependency of source Lemma 2, not a proof of the matrix inequality or frozen Target.

I checked the canonical README, solution, frozen Lean statement, and both coefficient-two Lemma 2 reviews against the five source hashes in the contract; all match. The source's positive eigenvalue satisfies `0<λ<1`, with `μ=λ/(1+λ)∈(0,1/2)` and `λ=μ/(1−μ)`. After cancelling the identical deficit term, the second inequality of source Equation (7) is exactly `λ(s+c)/2 ≤ μs+μ(2−μ)c/[2(1−μ)]`. The right-minus-left difference simplifies to `μ[s(1−2μ)+c(1−μ)]/[2(1−μ)]≥0` for `s,c>0`. Thus the proposed Lean theorem preserves the source coefficient `1/2`, the cutoff `c`, and the strict positive-eigenvalue interval, with no matrix claim smuggled into this scalar gate.

I independently recomputed both rational witnesses: `(s,c,λ)=(1,1,1/2)` gives `μ=1/3`, sides `1/2` and `3/4`, gap `1/4`; `(2,3,1/3)` gives `μ=1/4`, sides `5/6` and `11/8`, gap `13/24`. The `λ↓0` and `λ↑1` checks give limiting gaps `0` and `c/4`, but neither endpoint is added to the theorem. These exact values agree with the proposed statement and source orientation.

Implementation may use private denominator/positivity helpers but must expose only the frozen `ridgeCompression_eq7_scalar` type. Require a separate imported exact-signature/source/LeanCert `kernel` audit and standard-axiom report before aggregate import or use in the larger positive-part proof.
