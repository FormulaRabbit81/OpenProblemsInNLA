# SP-15 finite selection and final assembly: plan before implementation

Author: /root/mi13_full_referee2. Formalization contribution: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; substantial OpenAI Codex assistance. Preserve all prior mathematical
and code attribution. No email. This is author planning, not independent review.

The immediate implementation candidate is exact frozen contract 27. Contracts
28–29 are planned only as final assembly after the genuine spectral and arbitrary
unitary-injectivity dependencies are proved. Their absence must never be filled
by hypotheses, axioms, guessed witnesses, or a conditional result counted as the
original problem. All three frozen headers remain verbatim.

## Numerical statements first — arbitrary M, not a finite check

Take the ε > 0 and function ψ from the actual `local_coefficient_fiber` theorem.
For arbitrary M : ℕ, define the positive real denominator D = ((M+1 : ℕ) : ℝ),
the positive spacing δ = ε / D, and for i : Fin (M+1) put

    tᵢ = 1 + δ · (i.val : ℝ),       xᵢ = ψ(tᵢ).

The exact proof obligations are:

1. D > 0 and D ≠ 0 for every M, including M=0.
2. δ > 0 and δ D = ε by ordinary division cancellation, using D ≠ 0.
3. 0 ≤ (i.val : ℝ) < D from the actual finite index bound `i.isLt`.
4. |tᵢ−1| = δ·(i.val : ℝ) < δD = ε. Every chosen point is strictly inside the
   interval required by the local fiber; none is placed on its boundary.
5. If xᵢ = xⱼ, evaluate this equality at coordinate 9 and use ψ(t) 9 = t at
   both admissible arguments. Then tᵢ = tⱼ. Cancel the common addition of 1
   and the nonzero factor δ to obtain equality of the real natural casts,
   hence i.val = j.val and i = j.

For M=0 the unique index is 0, giving t₀ = 1. The same universal argument works;
there is no division by M, and no extra nonempty-index or M>0 assumption appears.
There is no need to approximate ε, evaluate ψ numerically, introduce a second
interval certificate, enumerate family sizes, or compute large matrices. The
already proved kernel-mode LeanCert box certificate remains consumed through
the genuine local-fiber dependency.

## Exact contract 27

Use the ε, positivity and ψ supplied by contract 15, which must have an actual
successful local proof before this implementation is checked. Define the finite
family exactly as above. The interval inequality gives all three conclusions
of contract 15 for every index. Retain its full `parameterBox` membership.

Prove `Function.Injective x` by coordinate-9 evaluation and the cancellation
argument above. Convert `coefficients (x i) = coefficients basePoint` to the
required `coefficientBaseValue` using the already proved exact
`coefficient_base_value`. Do not assume ψ itself is globally injective: only
the proved identity of its ninth-index coordinate on the admissible interval
is used. No continuity or invertibility beyond the proved local neighborhood
is needed.

Pinned elementary APIs suffice: `Nat.cast_pos`, `Nat.cast_lt`,
`Nat.cast_injective`, `Fin.ext`, `div_pos`, `div_mul_cancel₀`,
`mul_lt_mul_of_pos_left`, `abs_of_nonneg`, `add_left_cancel`, and
`mul_left_cancel₀`. Use a short symbolic ring normalization for tᵢ−1 if needed.
No `native_decide`, resource increase, approximate arithmetic, or custom axiom.

## Exact contract 28 — after both required transports are proved

Take x, injectivity, box membership and constant coefficient data from contract
27 and set A i = `constructedMatrix (x i)`. For every pair i,j, the equal
coefficient statements imply actual coefficient-function equality. Apply the
proved exact contract 21, `equal_coefficients_shifted_singular_values`, to get
`SuperIdentical (A i) (A j)`. This retains every complex shift and every ordered
singular-value index from the original definition; no sampled shifts suffice.

Given i<j and an alleged original `UnitarySimilar (A i) (A j)`, apply proved
contract 26, `constructed_unitary_injectivity`, to deduce x i = x j. Finite-family
injectivity then gives i=j, contradicting i<j. The unitary theorem must have
been proved for every U satisfying the original one-sided condition UᴴU=I;
a restricted set of intertwiners would not establish this contract.

Both dependencies 21 and 26 are currently outstanding. This plan does not
certify them or authorize replacing them with assumptions.

## Exact contract 29 — literal canonical negation

Assume `CanonicalFiniteness`. Instantiate it at n=9 with 1≤9 to obtain its
actual promised M≥1 and universal family assertion. Apply contract 28 at that
same M. Feed the resulting all-pairs `SuperIdentical` family into the promised
assertion to obtain i<j and unitary similarity. This contradicts contract 28's
non-similarity conclusion. The quantifier order, dimension-nine construction,
arbitrary M, and original predicates remain exactly the frozen definitions.

## Gates and source scope

Keep the thirteen protected files and their original targets unchanged. Bind
the actual current local-fiber/base-value sources and exact headers separately.
If local-fiber compilation fails or its source changes, authenticate the corrected
successful dependency before submitting contract 27 for checking. For contracts
28–29, first obtain actual complete implementations of the outstanding original
spectral and arbitrary-unitary transports. All new proof code awaits coordinator
acceptance of this plan. Root alone compiles serially with unchanged limits;
this author invokes no Lean, Lake, Git mutation, network, or Comparator.

No completed-original-target count changes until all 29 contracts, independent
reviews, required actual local checks and the final real Linux checks pass.
