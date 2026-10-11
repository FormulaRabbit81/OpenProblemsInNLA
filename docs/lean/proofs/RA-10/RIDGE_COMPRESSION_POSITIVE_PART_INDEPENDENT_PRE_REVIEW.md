# RA-10 coefficient-two ridge compression: independent pre-implementation review

**Reviewer:** `/root`. **Disposition:** approve the exact source statement and numerical contract in [RIDGE_COMPRESSION_POSITIVE_PART_PRE_REVIEW.md](RIDGE_COMPRESSION_POSITIVE_PART_PRE_REVIEW.md) for staged Lean implementation. This document certifies no Lean proof of the inequality or of the frozen `NLA.Statements.RA10.Target`.

I checked the precontract against the canonical `RA-10/solution.md` Lemma 2 and its use in Equation (13). The README, solution, frozen statement, and seven listed dependency hashes match the precontract. In particular, the source lemma says `tr((f_s(C)−f_s(A))₊) ≤ 2/(s+c)[tr((C−A)₊)+d]`, with `C=PAP`, `d=tr((cI_k−H)₊)`, and **coefficient two** for arbitrary `s,c>0`, including singular `H`. The already audited selected-compression support theorem identifies `d` with the full-space `tr((cP−C)₊)` without counting unselected zero directions.

The proposed public Lean theorem is the exact selected-projector application: `P=selectedProjection k QAhat`, `C=P*A*P`, `F_A=FunctionMatrix (ridgeAtom s) eigenvaluesA QA`, and `F_C=FunctionMatrix (ridgeAtom s) eigenvaluesC QC`. It requires the ordered PSD witnesses of `A`, `Ahat`, and this actual `C`, `1≤k<n`, `s>0`, and `c=eigenvaluesA[k−1]>0`. No equality or alignment of the independently supplied bases is assumed. Its right side uses `(C−A)₊` and `(cP−C)₊`; swapping either sign, using `eigenvaluesAhat[k−1]` for `c`, adding a gap or invertibility hypothesis, or increasing `2/(s+c)` would change the target. The `c=0` branch of the full problem remains a separate obligation.

I independently checked the manuscript's scalar Equation (7) arithmetic. With `μ=λ/(1+λ)` and `0<λ<1`, hence `0<μ<1/2` and `λ=μ/(1−μ)`, the difference between its two scalar sides is exactly

```text
μ [s(1−2μ) + c(1−μ)] / [2(1−μ)] ≥ 0.
```

At `μ=1/4`, `s=1`, `c=3`, that gap is `11/24`. This fixes the sign and factor of two in the eventual scalar Lean lemma. The Schur-complement argument, positive-eigenspace summation, and singular-compression limit in the source remain formal proof obligations; the precontract does not license them as assumptions.

As an independent orientation check, take `A=diag(3,1)`, let `P` project onto `(1,1)/√2`, so `C=2P`, and set `s=1,c=3`. Then `f_s(C)−f_s(A)` has positive-part trace `(√73−7)/24`, while `tr((C−A)₊)=√2−1` and `tr((cP−C)₊)=1`. The claimed right side is `√2/2`, larger than the left side. The source's `C=0`, `k=0`, and singular-`H` cases also require no hidden full-rank hypothesis. These numerical witnesses check indexing and orientation; they do not prove the general inequality.

Implement the original public signature verbatim, with the audited support theorem for `d`. Require a separate final review of the imported theorem's exact type, source locks, LeanCert `kernel` trust and axiom output, and the aggregate import before using it toward Equation (13) or the full target.
