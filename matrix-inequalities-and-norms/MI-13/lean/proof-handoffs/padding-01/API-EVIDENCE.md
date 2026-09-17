# Pinned API evidence

Local read-only source inspection; no compiler or network authentication was run for this packet. Mathlib is the accepted pin 0df444a360eaa60ab8c11dca51a86af692955474; core is the accepted Lean v4.33.1. Exact local file hashes and excerpts follow.

## Mathlib/Data/Matrix/Block.lean

Block entries, conjugate transpose, multiplication.

SHA256: `c15b7cd49955438bd2334788946fe742b9a827dd1fc485e2e70ef42885d5ea9e`.

Lines 45–67:

```lean
@[pp_nodot]
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (n ⊕ o) (l ⊕ m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) (fun j => Sum.elim (C j) (D j))

@[simp]
theorem fromBlocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
theorem fromBlocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl

@[simp]
theorem fromBlocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl

@[simp]
theorem fromBlocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
```

Lines 138–141:

```lean

theorem fromBlocks_conjTranspose [Star α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conjTranspose, fromBlocks_transpose, fromBlocks_map]
```

Lines 213–228:

```lean

theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α)
    (C' : Matrix m p α) (D' : Matrix m q α) :
    fromBlocks A B C D * fromBlocks A' B' C' D' =
      fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp only [fromBlocks, mul_apply, of_apply,
      Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, add_apply]

theorem fromBlocks_diagonal_pow [Semiring α] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n α) (D : Matrix m m α) (k : ℕ) :
    (fromBlocks A 0 0 D) ^ k = fromBlocks (A ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => ext (i | i) (j | j) <;> simp [one_apply]
  | succ n ih =>
```

## Mathlib/LinearAlgebra/Matrix/Reindex.lean

The same index equivalence preserves multiplication and addition.

SHA256: `8178dff6183ced5f5892ef4194adb9bffddb87a36dc2b7db9526d15d2371394c`.

Lines 78–91:

```lean

variable [Fintype m] [Fintype n] [Fintype o] [Mul R] [AddCommMonoid R]

/-- `Matrix.reindex` as a `RingEquiv` between `R`-matrices. -/
def reindexRingEquiv (e : m ≃ n) : Matrix m m R ≃+* Matrix n n R where
  __ := reindexAddEquiv R e e
  map_mul' A B := submatrix_mul_equiv A B .. |>.symm

@[simp]
theorem coe_reindexRingEquiv (e : m ≃ n) : ⇑(reindexRingEquiv R e) = reindex e e :=
  rfl

@[simp]
theorem toEquiv_reindexRingEquiv (e : m ≃ n) :
```

## Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

Fintype.sum_equiv is generated from the displayed prod_equiv by to_additive.

SHA256: `2f39541f66288cb9ae9f77d97fd3656825a1dd1a4b5ca6a156f938d8fa1678a8`.

Lines 728–746:

```lean
alias _root_.Function.Bijective.finset_sum := _root_.Function.Bijective.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_prod := _root_.Function.Bijective.finsetProd

/-- `Fintype.prod_equiv` is a specialization of `Finset.prod_bij` that
automatically fills in most arguments.

See `Equiv.prod_comp` for a version without `h`.
-/
@[to_additive /-- `Fintype.sum_equiv` is a specialization of `Finset.sum_bij` that
automatically fills in most arguments.

See `Equiv.sum_comp` for a version without `h`. -/]
lemma prod_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ x, f x = g (e x)) :
    ∏ x, f x = ∏ x, g x := prod_bijective _ e.bijective _ _ h

@[to_additive]
lemma _root_.Function.Bijective.prod_comp {e : ι → κ} (he : e.Bijective) (g : κ → M) :
```

## Mathlib/Data/Fintype/BigOperators.lean

Fintype.sum_sum_type is generated from prod_sum_type by to_additive.

SHA256: `bfa35992c02f47d7c78a5425ea3c4eecba0ad54de1b5752db565b37de11148c0`.

Lines 257–270:

```lean
variable {α₁ : Type*} {α₂ : Type*} {M : Type*} [Fintype α₁] [Fintype α₂] [CommMonoid M]

@[to_additive]
theorem Fintype.prod_sumElim (f : α₁ → M) (g : α₂ → M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disjSum _ _ _

@[to_additive (attr := simp)]
theorem Fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disjSum _ _ _

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type'`. -/
```

## Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean

Zero and reindexing commute with conjugate transpose.

SHA256: `10ace10899567db7c2ccd38c0e89e3bdca2261494975a42d3b1a5535c9e3b1b6`.

Lines 173–178:

```lean
  map_involutive star_involutive |>.eq_iff.trans <| by rw [map_diagonal_star]

@[simp]
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
  Matrix.ext <| by simp

```

Lines 439–448:

```lean
@[simp]
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r : l → m)
    (c : o → n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r :=
  ext fun _ _ => rfl

theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl

variable (m α) in
```

## Mathlib/Analysis/Normed/Lp/Matrix.lean

The actual toLpLin map preserves matrix multiplication as composition.

SHA256: `976400e4430cbe64214a24e37f3f98c807c30f1c9926c8cbd367ae2fd111e2f9`.

Lines 53–65:

```lean

/-- Note that applying this theorem needs an explicit choice of `q`. -/
theorem toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B := by
  ext; simp

/-- A copy of `toLpLin_mul` that works for `simp`, for the common case where the domain and codomain
have the same norm. -/
@[simp]
theorem toLpLin_mul_same [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p p (A * B) = toLpLin p p A ∘ₗ toLpLin p p B :=
  toLpLin_mul _ _ _ _ _

```

## Mathlib/Analysis/InnerProductSpace/PiL2.lean

toEuclideanLin is toLpLin 2 2 and is the orthonormal-basis toLin.

SHA256: `1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053`.

Lines 1238–1245:

```lean
namespace Matrix

variable [Fintype n] [DecidableEq n]

/-- A shorthand for `Matrix.toLpLin 2 2`. -/
abbrev toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
  toLpLin 2 2

```

Lines 1276–1282:

```lean
open EuclideanSpace in
lemma toEuclideanLin_eq_toLin_orthonormal [Fintype m] :
    toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 𝕜).toBasis :=
  rfl

end Matrix

```

## Mathlib/Analysis/InnerProductSpace/Adjoint.lean

Conjugate transpose is the actual Euclidean adjoint.

SHA256: `f28b5896638f712605265a69ffe4469f1f42e1b78b10ade0844738aeecd2b2a2`.

Lines 1052–1057:

```lean

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
theorem Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = A.toEuclideanLin.adjoint :=
  A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)
```

## Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean

The characteristic polynomial of toLin equals the matrix characteristic polynomial.

SHA256: `167cae25a064b15f836022f0441997349a236bd699ca87bcd93cf532b794529a`.

Lines 84–96:

```lean
namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp]
theorem charpoly_toLin (A : Matrix n n R) (b : Basis n R M) :
    (A.toLin b b).charpoly = A.charpoly := by
  simp [← LinearMap.charpoly_toMatrix (A.toLin b b) b]

@[simp]
theorem charpoly_toLin' (A : Matrix n n R) : A.toLin'.charpoly = A.charpoly := by
  rw [← Matrix.toLin_eq_toLin', charpoly_toLin]

```

## Mathlib/LinearAlgebra/Charpoly/Basic.lean

Every finite endomorphism characteristic polynomial is monic, hence nonzero.

SHA256: `46b0cf44b0ea659c6f881a87771da4400e0e807cff76365da1895d73338904ca`.

Lines 70–75:

```lean
section Coeff

theorem charpoly_monic : f.charpoly.Monic :=
  Matrix.charpoly_monic _

open Module in
```

## Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean

Zero blocks, reindexing, and block diagonal characteristic polynomials.

SHA256: `584eb12d39eacb591155c98cfa2089479d88cfdea8eb5f31ba5ed687de200a9a`.

Lines 152–164:

```lean
theorem charpoly_diagonal (d : n → R) : charpoly (diagonal d) = ∏ i, (X - C (d i)) := by
  simp [charpoly]

theorem charpoly_one : charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n := by
  simp [charpoly]

theorem charpoly_natCast (k : ℕ) :
    charpoly (k : Matrix n n R) = (X - (k : R[X])) ^ Fintype.card n := by
  simp [charpoly]

theorem charpoly_ofNat (k : ℕ) [k.AtLeastTwo] :
    charpoly (ofNat(k) : Matrix n n R) = (X - ofNat(k)) ^ Fintype.card n :=
  charpoly_natCast _
```

Lines 174–190:

```lean

lemma charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [charpoly, charmatrix_map, ← Polynomial.coe_mapRingHom, charpoly, RingHom.map_det,
    RingHom.mapMatrix_apply]

@[simp]
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]
```

## Mathlib/Analysis/InnerProductSpace/Spectrum.lean

Exact ordered eigenvalue list equals the decreasing sorted real roots with multiplicity.

SHA256: `f12ef613416053c759ef30179147744c64eeec90f7467644cb30e64d532d7aa6`.

Lines 367–378:

```lean
  simp

theorem sort_roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    (T.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn (hT.eigenvalues hn) := by
  simp_rw [hT.roots_charpoly_eq_eigenvalues, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  have := hn.symm
  convert! List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  convert! (hT.eigenvalues_antitone hn).sortedGE_ofFn

theorem eigenvalues_eq_eigenvalues_iff {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
```

## Mathlib/Analysis/InnerProductSpace/SingularValues.lean

Nonnegativity, out-of-range zero, and equality of squared singular value with Gram eigenvalue.

SHA256: `ce8193fcd5d226845a71f66b8ca7ad385358916a6e0e688745410ac412ed5c81`.

Lines 96–102:

```lean
    Finsupp.ofSupportFinite
      (fun i ↦ √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

theorem singularValues_nonneg (i : ℕ) : 0 ≤ T.singularValues i := by
  rw [singularValues, Finsupp.embDomain_apply, Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity
```

Lines 122–129:

```lean
  T.singularValues_fin hn ⟨i, hi⟩

theorem singularValues_of_finrank_le {i : ℕ} (hi : finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  simp [hi]

theorem sq_singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
```

## Mathlib/Algebra/Polynomial/Roots.lean

Roots of a nonzero product are the multiset sum; X^d contributes d zero roots.

SHA256: `162d86710afc10cc3ed158236994ed020e589f7fa15d5b39a30bd3e1f153080c`.

Lines 169–174:

```lean
  simp at hp

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, rootMultiplicity_mul hpq]
```

Lines 288–293:

```lean
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow, roots_X]

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
```

## Mathlib/Algebra/Order/Group/Multiset.lean

Natural multiples of singleton multisets are replicates.

SHA256: `37a8af5a66e5c250f23232a92636556e3992ccd5dc7c4d103ddddb6861c3a554`.

Lines 97–101:

```lean
lemma nsmul_replicate {a : α} (n m : ℕ) : n • replicate m a = replicate (n * m) a :=
  ((replicateAddMonoidHom a).map_nsmul _ _).symm

lemma nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a := by
  rw [← replicate_one, nsmul_replicate, mul_one]
```

## Mathlib/Data/Multiset/MapFold.lean

Map distributes over multiset addition and replicates.

SHA256: `838653964b2dc77afcf2303c4f4058af259cb2d7db36c290eac8e9c8cce57e00`.

Lines 82–90:

```lean
  rfl

@[simp]
theorem map_replicate (f : α → β) (k : ℕ) (a : α) : (replicate k a).map f = replicate k (f a) := by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]
theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ map_append
```

## Mathlib/Data/Multiset/AddSub.lean

Multiset addition of coerced lists is list append.

SHA256: `f271e3bbdb10db9312ba86547163961e8481a80c3e57d9f2e63c35ec0c8c1c4f`.

Lines 54–60:

```lean
instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

@[simp]
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl

```

## Mathlib/Data/Multiset/Replicate.lean

List replicate coerces to multiset replicate.

SHA256: `588a8574a7ce2c10afe9c3bb5d3c639086b164fa62cb4943aba1c63da1629679`.

Lines 34–39:

```lean
/-- `replicate n a` is the multiset containing only `a` with multiplicity `n`. -/
def replicate (n : ℕ) (a : α) : Multiset α :=
  List.replicate n a

theorem coe_replicate (n : ℕ) (a : α) : (List.replicate n a : Multiset α) = replicate n a := rfl

```

## Mathlib/Data/Multiset/Sort.lean

Sorted multisets retain all elements and multiplicities; sorting a coerced list uses mergeSort.

SHA256: `da36e6ab5437d2691f19cd8721c37d3f263c01f38385d26f1db3ed61628d2329`.

Lines 43–56:

```lean
theorem coe_sort : sort l r = mergeSort l (r · ·) :=
  rfl

@[simp]
theorem pairwise_sort : (sort s r).Pairwise r :=
  Quot.inductionOn s (pairwise_mergeSort' _)

@[simp]
theorem sort_eq : ↑(sort s r) = s :=
  Quot.inductionOn s fun _ => Quot.sound <| mergeSort_perm _ _

@[simp]
theorem sort_zero : sort 0 r = [] :=
  List.mergeSort_nil
```

## Mathlib/Data/List/Sort.lean

An already pairwise ordered list is fixed by mergeSort.

SHA256: `672d712325b3e9fe3ca33c4c76cc6e850d750672ece00c2ad2805607569e0757`.

Lines 338–346:

```lean
theorem pairwise_mergeSort' (l : List α) : Pairwise r (mergeSort l (r · ·)) := by
  simpa using pairwise_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

variable [Std.Antisymm r]

theorem mergeSort_eq_self {l : List α} : Pairwise r l → mergeSort l (r · ·) = l :=
```

## Mathlib/Data/List/Pairwise.lean

A repeated zero list is pairwise ordered by reflexivity.

SHA256: `0b110f80add05b7d54dd74f27d89a472ca7ea1b7eb4963788e07335d310f4312`.

Lines 110–116:

```lean
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)

theorem pairwise_replicate_of_refl {n} [Std.Refl R] : (replicate n a).Pairwise R :=
  pairwise_replicate.mpr (Or.inr <| refl_of ..)

/-! ### Pairwise filtering -/
```

## Mathlib/Data/List/GetD.lean

getD relates finite lookup to default zero and treats appended zeros exactly.

SHA256: `574a0a3994484d8d591a1f57604a0eefd6b8947b1b5c9b698b01dd8bf48e600a`.

Lines 29–48:

```lean
section getD

variable (d : α)

theorem getD_eq_getElem {n : ℕ} (hn : n < l.length) : l.getD n d = l[n] := by
  grind

theorem getD_eq_getElem? (i : Fin l.length) : l.getD i d = l[i]?.get (by simp) := by
  simp only [getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, Fin.getElem_fin,
    Option.get_some]

theorem getD_eq_get (i : Fin l.length) : l.getD i d = l.get i :=
  getD_eq_getElem ..

theorem getD_map {n : ℕ} (f : α → β) : (map f l).getD n (f d) = f (l.getD n d) := by
  simp only [getD_eq_getElem?_getD, getElem?_map, Option.getD_map]

theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getD n d = d := by
  grind

```

Lines 62–77:

```lean

@[simp]
theorem getElem?_getD_replicate_default_eq (r n : ℕ) : (replicate r d)[n]?.getD d = d := by
  grind

theorem getD_replicate {y i n} (h : i < n) : getD (replicate n x) i y = x := by
  grind

theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  grind

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  grind

```

## Mathlib/Analysis/RCLike/Basic.lean

The real part of complex zero is zero.

SHA256: `a84c795cd067befa1095540ddacd3f580d3d517f91c50965227c6f8e7e34474e`.

Lines 144–150:

```lean
  algebraMap.coe_zero

@[rclike_simps]
theorem zero_re : re (0 : K) = (0 : ℝ) :=
  map_zero re

@[rclike_simps]
```

## Init/Data/List/OfFn.lean

The length and indexed entries of ofFn; membership is an actual finite index.

SHA256: `e2054feea94eea72e5ddca3145b03e9e669db8bb89cf8d0286354fdd2dfb9de2`.

Lines 43–64:

```lean
@[simp, grind =]
theorem length_ofFn {f : Fin n → α} : (ofFn f).length = n := by
  simp only [ofFn]
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, ih]

@[simp, grind =]
protected theorem getElem_ofFn {f : Fin n → α} (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp_all⟩ := by
  simp only [ofFn]
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    match i with
    | 0 => simp [Fin.foldr_succ]
    | i+1 =>
      simp only [Fin.foldr_succ]
      apply ih
      simp_all

@[simp, grind =]
```

Lines 113–117:

```lean
@[simp 500, grind =]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
```

## Init/Data/List/Pairwise.lean

Pairwise order on append is two internal orders plus all cross comparisons.

SHA256: `0dbf6798e805477e651b1ff6fe472f5fb14beb37d6883167d36a81cba9c122ed`.

Lines 156–159:

```lean
@[grind =] theorem pairwise_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ <;> simp [*, or_imp, forall_and, and_assoc, and_left_comm]

```

## Init/Data/List/Lemmas.lean

Every member of replicate is the repeated value.

SHA256: `0724ebc7c72c87ad6d480dba407c43cc60393e7a0facfbaa6670045f66f636ac`.

Lines 2204–2208:

```lean

@[simp, grind =] theorem mem_replicate {a b : α} : ∀ {n}, b ∈ replicate n a ↔ n ≠ 0 ∧ b = a
  | 0 => by simp
  | n+1 => by simp [replicate_succ, mem_replicate, Nat.succ_ne_zero]

```

Lines 2216–2219:

```lean
    split <;> simp_all

@[grind →] theorem eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a := (mem_replicate.1 h).2

```
