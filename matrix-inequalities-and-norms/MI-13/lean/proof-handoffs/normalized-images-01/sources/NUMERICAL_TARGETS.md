# MI-13 numerical boundary — before Lean statements or proof code

For every natural `m,n` with `2 ≤ m` and `2 ≤ n`, every complex
`A,C : Matrix (Fin m) (Fin n) ℂ` and `B : Matrix (Fin n) (Fin m) ℂ`, prove

```
frobeniusNorm (A * B * C - C * B * A)^2
  ≤ 2 * spectralNorm B^2
      * (singularValue A 0^2 + singularValue A 1^2)
      * frobeniusNorm C^2.
```

Multiplication is the actual rectangular matrix product. `frobeniusNorm` is
the norm after flattening all entries into complex Euclidean space, and is
required to equal both the square root of the sum of squared entry norms and
the square root of the real trace of `A* A`. `spectralNorm` is the norm of
the actual continuous linear map between complex Euclidean spaces.
`singularValue A k` is Mathlib's actual zero-indexed, decreasing, nonnegative,
zero-extended singular-value sequence of the same underlying linear map.
The equality of its first entry with the operator norm and its squared entries
with the ordered Gram eigenvalues are explicit proof obligations.

There is no dimension bound, rank assumption, invertibility assumption,
reality restriction, distinct-eigenvalue hypothesis, entry-size bound or
generic-matrix exclusion. All zero and deficient-rank cases are included.
The coefficient is exactly two; replacing it by a larger constant would not
solve this target. Repeated and zero singular values must be retained.

The only planned LeanCert certificate is the exact scalar fact

```
0 < (1/2 : ℝ)  and  (1/2 : ℝ) + 1/2 = 1.
```

Use `interval_decide (trust := kernel)` for the strict positivity, at one
exact rational input and the least adequate precision. Prove the equality
symbolically. The positivity certificate must be used by the squared
Frobenius averaging argument. No interval subdivision, matrix enumeration,
approximate spectrum or dimension-dependent computation is planned.

All other estimates are symbolic. In particular, for nonnegative real `s,t`
and complex `p,q`, prove

```
‖(s:ℂ)*p - (t:ℂ)*q‖² ≤ (s²+t²)*(‖p‖²+‖q‖²).
```

For `0 ≤ d ≤ 1`, prove exactly that `d ± i sqrt(1-d²)` have squared modulus
one and average `d`. This is a universal real-algebraic/square-root identity,
not a finite set of interval tests.

The exact endpoint is `A=diag(1,-1)`, `B=I₂`, `C=e₁₂`: the squared
commutator Frobenius norm is four, `‖B‖op²=1`, both first squared singular
values of A are one, and `‖C‖F²=1`. This checks normalization and sharpness;
it does not replace the universal theorem.

The canonical source is the complete retained MI-13 page at upstream commit
`ebdf2f34dc7690d8e323faaeb40d6dcc30c851ff`. It credits Nobori's question and
Audenaert's refined commutator theorem. This project must **prove the refined
commutator bound internally**; it cannot assume that theorem or put it in a
definition. The repository's complete reduction and all earlier attribution
remain credited. No new priority claim is made.

This document is a pre-code proposal. No Lean statement elaboration, proof,
LeanCert execution, Comparator run, immutable statement freeze, publication or
verified count is asserted. Two independent statement reviews and actual local
elaboration must precede proof implementation; fresh non-root Linux verification
is a separate final gate.
