# Coefficient API evidence

Source-only inspection at the accepted Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`; no compiler was invoked. Existing literal-pin authentication is reused where its exact hash matches. Newly inspected library files are bound to the accepted local pinned source without claiming a fresh remote fetch.

## Mathlib/Algebra/Polynomial/OfFn.lean

toFn, coefficient and degree semantics of ofFn, finite monomial sum, reverse roundtrip. Source SHA256 `efe78ed6e903a951eb7cbc34846059384edbe2658a40be20d8bac74b12451b11`.

Lines 33–37:

```lean
/-- `toFn n f` is the vector of the first `n` coefficients of the polynomial `f`. -/
noncomputable def toFn (n : ℕ) : R[X] →ₗ[R] Fin n → R := LinearMap.pi (fun i ↦ lcoeff R i)

theorem toFn_zero (n : ℕ) : toFn n (0 : R[X]) = 0 := by simp

```

Lines 68–102:

```lean
set_option backward.isDefEq.respectTransparency false in
/-- If `i < n` the `i`-th coefficient of `ofFn n v` is `v i`. -/
@[simp]
theorem ofFn_coeff_eq_val_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

set_option backward.isDefEq.respectTransparency false in
/-- If `n ≤ i` the `i`-th coefficient of `ofFn n v` is `0`. -/
@[simp]
theorem ofFn_coeff_eq_zero_of_ge {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) :
    (ofFn n v).coeff i = 0 := by
  simp [ofFn, Nat.not_lt_of_ge hi]

/-- `ofFn n v` has `natDegree` smaller than `n`. -/
theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  exact fun _ h ↦ ofFn_coeff_eq_zero_of_ge _ <| Nat.le_of_pred_lt h

/-- `ofFn n v` has `degree` smaller than `n`. -/
theorem ofFn_degree_lt {n : ℕ} (v : Fin n → R) : (ofFn n v).degree < n := by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
      <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _

theorem ofFn_eq_sum_monomial {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, monomial i (v i) := by
  by_cases h : n = 0
  · subst h
    simp [ofFn]
  · rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

```

Lines 117–125:

```lean
  ext i
  by_cases! h : i < n
  · simp [h, toFn]
  · have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt <| by lia
    simp [*]

end ofFn

end Polynomial
```

## Mathlib/Algebra/Polynomial/Basic.lean

C a times X^n equals the coefficient monomial. Source SHA256 `9c53d094b3e3beacac81c52bcd48fe1723b51ecfda1c234c67cbbe15f61f19bb`.

Lines 661–665:

```lean
theorem C_mul_X_pow_eq_monomial : ∀ {n : ℕ}, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial, mul_one]

```

## Mathlib/Algebra/Polynomial/Degree/Defs.lean

Strict natDegree/degree equivalence requires a nonzero polynomial. Source SHA256 `ff616e11c821c0baac9f9f4adb43b28eb1b442ef5e4752a9f8d3469350af7ffc`.

Lines 136–141:

```lean
theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  WithBot.unbotD_le_iff (fun _ ↦ bot_le)

theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hp))

```

## Mathlib/Analysis/Normed/Lp/PiLp.lean

Actual WithLp function coercion and PiLp.ext. Source SHA256 `660f3ad7077490c9a8eae924e18731c400282b8dccf80bfec1c6b02fe11ee25f`.

Lines 85–99:

```lean
abbrev PiLp (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : Type _ :=
  WithLp p (∀ i : ι, α i)

/-The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithLp.equiv`. -/
instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : CoeFun (PiLp p α) (fun _ ↦ (i : ι) → α i) where
  coe := ofLp

instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨toLp p fun _ => default⟩

@[ext]
protected theorem PiLp.ext {p : ℝ≥0∞} {ι : Type*} {α : ι → Type*} {x y : PiLp p α}
    (h : ∀ i, x i = y i) : x = y := ofLp_injective p <| funext h

```

## Mathlib/Analysis/InnerProductSpace/PiL2.lean

Euclidean inner product and squared norm are the coordinate sums. Source SHA256 `1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053`.

Lines 102–105:

```lean

theorem PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι → Type*} [∀ i, NormedAddCommGroup (f i)]
    [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl
```

Lines 146–154:

```lean

theorem EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2) := by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using! congr_arg ((↑) : ℝ≥0 → ℝ) x.nnnorm_eq

theorem EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x

```

## Mathlib/Analysis/InnerProductSpace/Basic.lean

The first scalar inner-product argument is conjugated. Source SHA256 `344aa5e0b104223d327bb1f13db092b4d320017c8f82b7ba9846b5f517222468`.

Lines 911–915:

```lean
theorem RCLike.inner_apply (x y : 𝕜) : ⟪x, y⟫ = y * conj x :=
  rfl

/-- A version of `RCLike.inner_apply` that swaps the order of multiplication. -/
theorem RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y := mul_comm _ _
```

## Mathlib/Algebra/Polynomial/Coeff.lean

The product coefficient is a finite antidiagonal sum. Source SHA256 `9afce0783702a4d23d7eab6cb0248845c0954b9d4c0bb0639e23d25238d604e5`.

Lines 108–116:

```lean

/-- Decomposes the coefficient of the product `p * q` as a sum
over `antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`. -/
theorem coeff_mul (p q : R[X]) (n : ℕ) :
    coeff (p * q) n = ∑ x ∈ antidiagonal n, coeff p x.1 * coeff q x.2 := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp_rw [← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.coeff_mul_antidiag p q n _ Finset.mem_antidiagonal
```

## Mathlib/Algebra/BigOperators/NatAntidiagonal.lean

Antidiagonal swap and range-sum conversion via to_additive. Source SHA256 `64430c09500e0d0d7592534812ef6db6c51dea382ba8448b0a90cd3b60392d14`.

Lines 35–40:

```lean

@[to_additive]
theorem prod_antidiagonal_swap {n : ℕ} {f : ℕ × ℕ → M} :
    ∏ p ∈ antidiagonal n, f p.swap = ∏ p ∈ antidiagonal n, f p := by
  conv_lhs => rw [← map_swap_antidiagonal, Finset.prod_map]
  rfl
```

Lines 55–68:

```lean

@[to_additive]
theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : ℕ × ℕ → M)
    (n : ℕ) : ∏ ij ∈ antidiagonal n, f ij = ∏ k ∈ range n.succ, f (k, n - k) :=
  Finset.prod_map (range n.succ) ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.mk.inj h).1⟩ f

/-- This lemma matches more generally than `Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ← `. -/
@[to_additive /-- This lemma matches more generally than
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` when using `rw ← `. -/]
theorem prod_antidiagonal_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    ∏ ij ∈ antidiagonal n, f ij.1 ij.2 = ∏ k ∈ range n.succ, f k (n - k) :=
  prod_antidiagonal_eq_prod_range_succ_mk _ _
end Nat
```

## Mathlib/Data/Fintype/BigOperators.lean

Fin-index sum and natural range sum coincide via to_additive. Source SHA256 `bfa35992c02f47d7c78a5425ea3c4eecba0ad54de1b5752db565b37de11148c0`.

Lines 223–231:

```lean

/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive /-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/]
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ i : Fin n, f i = ∏ i ∈ range n, f i :=
  calc
    ∏ i : Fin n, f i = ∏ i : { x // x ∈ range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i ∈ range n, f i := by rw [← attach_eq_univ, prod_attach]
```

## Mathlib/Algebra/Polynomial/Reverse.lean

Reflection uses the fixed bound N, with revAt N i=N-i for i≤N. Source SHA256 `6374fae31daa5e1003badc766bb7497a54904dc8c3091cb0ead225cf034824f7`.

Lines 59–66:

```lean
  rfl

@[simp, grind =]
theorem revAt_invol {N i : ℕ} : (revAt N) (revAt N i) = i :=
  revAtFun_invol

@[simp]
theorem revAt_le {N i : ℕ} (H : i ≤ N) : revAt N i = N - i :=
```

Lines 93–101:

```lean
    (reflect N f).support = Finset.image (revAt N) f.support := by cases f; ext1; simp [reflect]

@[simp, grind =]
theorem coeff_reflect (N : ℕ) (f : R[X]) (i : ℕ) : coeff (reflect N f) i = f.coeff (revAt N i) := by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    f.coeff.embDomain (revAt N) i
      = f.coeff.embDomain (revAt N) (revAt N (revAt N i)) := by rw [revAt_invol]
```

## Mathlib/Algebra/Polynomial/Eval/Coeff.lean

Mapping coefficients by the complex star ring endomorphism. Source SHA256 `e50ab9bdc373e93d51ebdbfbac8dccf066f6316052a4e5f9326ab9433ff613f2`.

Lines 74–82:

```lean

variable [Semiring S]
variable (f : R →+* S)

@[simp]
theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) := by
  rw [map, eval₂_def, coeff_sum, sum]
  simp_all

```

## Mathlib/Data/Finset/NatAntidiagonal.lean

Natural antidiagonal instance, including zero. Source SHA256 `b31b937894116044759339d87e6c0a160b917ba0058f625fd8e43b459f9f51b8`.

Lines 36–45:

```lean

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`. -/
instance instHasAntidiagonal : HasAntidiagonal ℕ where
  antidiagonal n := ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
  mem_antidiagonal {n} {xy} := by
    rw [mem_def, Multiset.Nat.mem_antidiagonal]

lemma antidiagonal_eq_map (n : ℕ) :
    antidiagonal n = (range (n + 1)).map ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.ext_iff.1 h).1⟩ :=
```

## Lean core Init/Data/Nat/Lemmas.lean

SHA256 `8259037db9a9bf223c4d57eb7811ff0b65e4439f98ed0bf3cd301565ff46daad`.

```lean
protected theorem sub_sub_self {n m : Nat} (h : m ≤ n) : n - (n - m) = m :=
  (Nat.sub_eq_iff_eq_add (Nat.sub_le ..)).2 (Nat.add_sub_of_le h).symm
```
