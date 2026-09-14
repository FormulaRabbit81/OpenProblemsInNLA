# Mathematical audit map

## Status

The full AC-04 target is **not proved or disproved**. The package presents a partial upper-bound result. The argument has not been independently refereed and has not been translated into Lean or another proof assistant.

## Dependency chain

1. **Exact tensor algebra (report Section 2).** An invertible complex basis change sends the requested tensor to a nonzero multiple of the six-permutation tensor. Four sign vectors give an exact rank-four decomposition. Its flattening rank is three. All 27 coefficients of both identities are checked separately.
2. **Extraction mechanism (Sections 3–4).** The report reproves the relevant kernel-compression argument from Alman–Li's framework, including the exact isolation and source-fullness properties. The base construction is checked with exact matrices: source contraction size 72 and rank 72; annihilator dimensions 45; extracted matrix rank 18; selected 18-by-18 minor determinant -1.
3. **Iteration (Section 5).** Fullness and isolation permit another application after squaring. The dimension recurrence is proved by induction; its closed form is verified by exact integer regression tests. The large higher-step tensors are not explicitly materialized.
4. **External spectral theorem (Section 6).** Strassen duality and the matrix-multiplication spectrum properties are invoked from the published literature. The certificate code does not prove them. The three slice orientations have exponents in [0,1] with sum at least two; symmetry supplies a useful orientation with exponent at least 2/3.
5. **All-parameter analysis (Section 6.1).** The normalized recurrence is analytically increasing in the exponent for fixed x in [0,64]. A grid search is not substituted for this proof.
6. **Exact scalar arithmetic (Section 7).** Integer cube-root enclosures and rational interval arithmetic prove `p_3((3.923038)^3,2/3)/68^8 > 1`. The narrow root bracket is separately certified. No floating-point comparison enters either decision.
7. **Scope of the obstruction (Section 8).** The formal assignment 3.9 satisfies the listed scalar inequalities for every iteration by a uniform induction. It is not asserted to extend to a spectral point on all tensors and therefore is not an asymptotic-rank lower bound.

## Deliberately excluded conclusions

- Asymptotic rank equals 3.
- Asymptotic rank is greater than 3.
- An explicit rank decomposition of the 24th power at the reported asymptotic constant.
- Global optimality of the initial power or of binary re-extraction.
- A new general speedup theorem.
- Research priority for this numerical refinement.
- Independent mathematical peer review or proof-assistant verification.
- An equivalence between AC-04 and the matrix multiplication exponent being 2; only the known forward implication is stated.

## Reproduction evidence

Both certificate programs and all eight regression tests passed in the delivered run. The scalar checker uses the standard library. The finite matrix audit uses SymPy 1.14.0. The exploratory table uses mpmath 1.3.0, and is kept separate from the proof certificate.

The rendered PDF was checked for clipping, overlap, and formula layout. This is a document-quality check, not mathematical verification.
