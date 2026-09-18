# MF-18 — exact numerical obligation

The entire fixed numerical obligation is frozen contract C01:

```lean
NLA.MF18.certified_half : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
```

Both fractions are exact real interpretations of the rational $1/2$. There
are no floating-point inputs, sampled matrix dimensions, approximated
eigenvalues, input files or parameter grids. The proof is in
`NLA/MF18/Numerical.lean` and explicitly uses kernel trust:

```lean
set_option leancert.trust "kernel"
constructor <;> interval_decide (trust := kernel)
```

The positive-half projection is consumed by `positive_average_and_sign` when
averaging the positive-definite matrices supplied by circle positivity.
That lemma feeds the homotopy nonvanishing argument, root selection and the
final complex rank theorem. The final proof therefore uses the certificate.
The upper-half conjunct is retained in the frozen numerical target; we do not
claim it is independently needed by the mathematical averaging argument.

The actual elaborated-body route recorded by root local341 is:

```text
canonical_full_complex_rank
  → full_complex_rank
  → limiting_equation_and_spectra
  → complementary_stability
  → complementary_closed_disk_nonvanishing
  → regularized_root_count
  → homotopy_boundary_nonvanishing
  → positive_average_and_sign
  → certified_half
```

The same graph reaches both `certified_half._proof_1_7` and
`certified_half._proof_1_15`, and the checked declaration
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. These are actual
proof-body edges, not a search for a theorem name in source comments. The
complete four paths are retained in [IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json)
and the local341 diagnostic comparison. The certificate's first successful
origin is root local295; its unchanged source and compiled output are
authenticated through the reuse chain in the successful local340 closure.

Only root executed Lean. The source reviewers replayed read-only Python
integrity checks over those receipts, logs and diagnostic dumps. All configured
theorems retain only the permitted standard axioms `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`, oracle or literature axiom is
accepted. `#assert_trust kernel` checks are present for all 25 final exports.
The later non-root Linux run 35315336123 passed at immutable proof commit `0d3a658789510d3cdd14729f22165219f7e7eaf8`; [its evidence](verification/linux-2026-09-18/README.md) is distinct from local341 and the source reviews.

LeanCert is pinned to `621a43d7cf21f87872392a01e874f2f1dbddc926` with Lean
`v4.33.1`. The minimal certificate pattern follows MF05's numerical module;
its authorship and the separately pinned Forsythe/Schiffer workflow patterns
are recorded in [SOURCE-ATTRIBUTION.json](SOURCE-ATTRIBUTION.json). The remaining
matrix, polynomial, topology and rank arguments are symbolic Lean proofs.
