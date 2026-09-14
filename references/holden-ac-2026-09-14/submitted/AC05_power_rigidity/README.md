# AC-05: tensor-power rigidity and exact lower bounds

**This package does not resolve AC-05.** It proves structural statements for every tensor power of specified hard families, and lower bounds compatible with asymptotic rank three. It does not improve the inherited asymptotic-rank upper bounds.

Start with `report/AC05_power_rigidity.pdf` (18 pages). The editable source is beside it.

## Main results

Write `F_lambda = Q_lambda + e_111`, where `Q_lambda` has coefficient one on 012, 021, 102, 120, 201 and coefficient lambda on 210. Let `U` have coefficient one on 002, 021, 111, 120, 201, 210, and let `P = Q_1`.

For parameters outside `{0,-1}`, two grouped products of F tensors are equivalent under arbitrary changes of basis on the three large factors exactly when the parameter multisets agree up to reciprocation. The same statement holds for Q products. A same-format degeneration from an F product to a Q product exists exactly under this condition; a degeneration in the other direction does not exist. A common finite product of the generic F and Q families cannot cancel a mismatch of parameter multisets. The U target remains separate after every finite blocking.

The proof includes a general three-subspace lemma: under the stated scalar-pair-intersection hypothesis, the stabilizer Lie algebra of a grouped product has no additional nonlocal relations. The hypothesis is essential, as a diagonal-tensor negative control demonstrates.

For every m >= 1, with N = 3^m, the report proves border-rank lower bounds `(3N-1)/2` for U, F_1 and P powers; and `(3N+1)/2` for F_lambda powers when lambda is neither zero nor one. The latter also applies to Q_lambda powers when lambda avoids zero, one and minus one. These bounds have exponential base three, not a base greater than three.

## Reproduce

With Python 3.10 or later:

```bash
python code/verify_manifest.py
python code/replay_certificates.py
python code/audit_inherited.py
```

Run the manifest check before regenerating results, since reruns can update recorded timing fields. It checks integrity, not mathematical correctness.

The replay uses only the standard library. The recorded run used Python 3.13.5. It passed 36 check groups, including 163 successful determinant evaluations, 13 product-action cases through third powers, character-configuration checks and four damaged-certificate rejection tests.

To regenerate the certificates with the recorded dependency:

```bash
python -m pip install -r requirements.txt
python code/generate_certificates.py
python code/replay_certificates.py
```

To rebuild the report with pdfLaTeX:

```bash
bash build_report.sh
```

`python code/replay_certificates.py --quick` skips third-power and character-configuration enumeration. It does not replace the full recorded run.

## What checks prove

For a size-n matrix with entries affine-linear in lambda, the determinant has degree at most n. Verifying a claimed determinant at n+1 exact integer nodes proves the polynomial identity. Explicit annihilating kernel vectors provide the matching rank upper bound. Product examples use exact modular rank lower bounds and integer kernel vectors.

The infinite-product theorem, convex-polytope normalizer arguments, and geometric invariant theory deductions are mathematical proofs in the report, not conclusions extrapolated from finite tests. The replay does not formalize those proofs or settle the asymptotic-rank conjecture.

## Inherited work

`baseline/AC05_rank_speedup.zip` is unchanged, SHA-256:

```text
2302fab337a4fef596fe6b327d1b02445af29035387df6331f6f99fb4eb22e45
```

Its standard-library finite-certificate replay passed again. Its reported upper bounds remain 4.64429449 for all complex 3-by-3-by-3 tensors and 3.92304 for those of border rank at most four. The current structural theorems do not depend on those upper bounds or on the inherited dimension-three component classification.

No external peer review, independent authorship, formal proof-assistant verification, or novelty claim is asserted. No repository files or status were modified. See `STATUS.md` and `SOURCES.md`.
