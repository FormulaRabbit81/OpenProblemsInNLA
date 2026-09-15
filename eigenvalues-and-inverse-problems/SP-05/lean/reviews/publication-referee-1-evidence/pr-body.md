## Complete result

Formally verify SP-05 for every real symmetric positive definite pair and every dimension n≥2: both actual symmetric/skew-sector Rayleigh minima are attained, and the symmetric minimum is no larger. The stronger source theorem gives a real nonzero PSD eigenmatrix at the positive global minimum of the actual Jordan–Kronecker product in every n≥1.

Six exact statements were independently approved before proof implementation. The proof uses literal column vectorization, Kronecker coefficients and commutation matrix, symbolic inverse-cone and modulus arguments, and an explicitly consumed LeanCert kernel certificate. Both independent full-source and operational reviews passed under the repository's Tau Ceti adaptation.

## Verification and preservation

- Authoritative Linux [run 35030259545, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35030259545/attempts/1), proof revision `9c8369dcea69f9f243a0502fb7e89beaa8f49fad`: actual Lean4 Comparator, default-kernel replay, only `propext`, `Classical.choice`, `Quot.sound`, and all required rejection/sandbox controls passed. All 92 submitted project inputs are bound to the retained receipt and original artifact.
- Pinned Lean 4.33.1, Mathlib and LeanCert; actual Comparator infrastructure follows pinned Forsythe and Schiffer references. Complete metadata, reproduction instructions, original artifact and independent reviews are retained.
- Permanent ID/path, complete original statement, original Colbrook proof and Kalantarova–Tunçel conjecture attribution are preserved. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology; substantial AI assistance disclosed, no contact email added.
- Promote only SP-05 to Lean verified; regenerate the catalog after permanent-ID validation and all 17 ID tests. Updated metadata covers all six exports. The regenerated three-page PDF preserves the complete target on one page; two narrow SP-05 renderer branches preserve layout and label the date as a verification check.

No external human review, official Tau Ceti endorsement or second independent Linux execution is claimed. Publication changes affect documentation, evidence, status, indexes and rendering; the reviewed mathematical inputs are unchanged. Final branch/PR CI will verify the complete published project again.
