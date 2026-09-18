/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The Epperlein--Wirth target and Barabanov/Wirth, Chitour--Mason--Sigalotti and
Morris background keep their original attribution. Reused MF05/MF07 results
retain Matthew J. Colbrook's mathematical attribution and source authorship.

Independent statement-only Comparator obligations for the complete original
MF-06 target. Every `sorry` is an intentional Challenge placeholder. No proof
implementation, statement approval, Lean elaboration, freeze or Comparator run
is claimed for MF-06. Two nonauthor statement reviews and root-controlled
typechecking/freeze must precede proof bodies. Solution must not import Challenge.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Topology
open Filter

noncomputable section
namespace NLA.MF05
open NLA.MF07

/-- C01. Exact reuse of the published kernel-mode certificate. Its positive
half is to be consumed in the cone-growth and neighborhood-shrinking arguments. -/
theorem half_radius_certificate : 0 < localRadius ∧ localRadius < 1 := by
  sorry

/-- C02. Exact reuse of the full canonical spectral sup-inf correspondence,
including attained nearest generators for arbitrary nonempty compact sets. -/
theorem spectral_hausdorff_semantics {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty) :
    IsCompact (spectralImage M) ∧ IsCompact (spectralImage N) ∧
    Metric.hausdorffEDist (spectralImage M) (spectralImage N) ≠ ⊤ ∧
    spectralHausdorff M N = canonicalHausdorff M N ∧
    0 ≤ spectralHausdorff M N ∧
    spectralHausdorff M N = spectralHausdorff N M ∧
    (spectralHausdorff M N = 0 ↔ M = N) ∧
    (∀ A ∈ M, ∃ B ∈ N,
      pointFamilyDistance A N = spectralNorm (A - B) ∧
      spectralNorm (A - B) ≤ spectralHausdorff M N) ∧
    (∀ B ∈ N, ∃ A ∈ M,
      pointFamilyDistance B M = spectralNorm (B - A) ∧
      spectralNorm (B - A) ≤ spectralHausdorff M N) := by
  sorry

/-- C03. Exact reuse: the actual all-word root infimum equals the canonical
limit at every radius, including zero. No radius-one hypothesis is hidden here. -/
theorem general_root_limit_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    0 ≤ jointSpectralRadius M ∧ jointSpectralRadius M ≤ familyNorm M ∧
    Tendsto (rootGrowth M) atTop (𝓝 (jointSpectralRadius M)) := by
  sorry

/-- C04. Exact reuse of positive homothety for all word lengths and radii. -/
theorem positive_scaling_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (c : ℝ) (hc : 0 < c) :
    IsCompact (scaledFamily c M) ∧ (scaledFamily c M).Nonempty ∧
    familyNorm (scaledFamily c M) = c * familyNorm M ∧
    (∀ n : ℕ, familyGrowth (scaledFamily c M) n = c ^ n * familyGrowth M n) ∧
    jointSpectralRadius (scaledFamily c M) = c * jointSpectralRadius M := by
  sorry

end NLA.MF05

namespace NLA.MF06
open NLA.MF07 NLA.MF05

/-- C05. The concrete word supremum is a continuous genuine complex norm.
It is supplied by a theorem, never by an assumed extremal-norm structure. -/
theorem bounded_envelope_norm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    IsComplexNorm (boundedEnvelope M) ∧ Continuous (boundedEnvelope M) ∧
    (∃ K : ℝ, 1 ≤ K ∧ ∀ x : EuclideanVector d,
      ‖x‖ ≤ boundedEnvelope M x ∧ boundedEnvelope M x ≤ K * ‖x‖) ∧
    (∀ A ∈ M, ∀ x : EuclideanVector d,
      boundedEnvelope M (applyMatrix A x) ≤ boundedEnvelope M x) := by
  sorry

/-- C06. The actual finite-tail suprema decrease to the defined infimum,
uniformly on every compact set. The limit is a continuous complex seminorm. -/
theorem tail_seminorm_limit {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    (∀ n : ℕ, Continuous (tailEnvelope M n)) ∧
    (∀ x : EuclideanVector d, Antitone (fun n : ℕ => tailEnvelope M n x)) ∧
    (∃ p : Seminorm ℂ (EuclideanVector d), ∀ x, p x = stableGauge M x) ∧
    Continuous (stableGauge M) ∧
    (∀ x : EuclideanVector d, stableGauge M x ≤ boundedEnvelope M x) ∧
    (∀ K : Set (EuclideanVector d), IsCompact K →
      TendstoUniformlyOn (tailEnvelope M) (stableGauge M) atTop K) := by
  sorry

/-- C07. Attainment of the max recurrence for the actual seminorm limit. -/
theorem stable_gauge_max_recurrence {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    ∀ x : EuclideanVector d,
      (∀ A ∈ M, stableGauge M (applyMatrix A x) ≤ stableGauge M x) ∧
      ∃ A ∈ M, stableGauge M (applyMatrix A x) = stableGauge M x := by
  sorry

/-- C08. The zero set of the actual limit is a proper invariant submodule
with strictly exponentially decaying restricted word actions. S=bottom is
allowed. The nonzero quotient and strict stability are conclusions. -/
theorem stable_kernel_exponential {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (hradius : jointSpectralRadius M = 1) :
    ∃ S : Submodule ℂ (EuclideanVector d),
      (∀ x : EuclideanVector d, x ∈ S ↔ stableGauge M x = 0) ∧
      S ≠ ⊤ ∧ FamilyInvariant M S ∧
      ∃ q K : ℝ, 0 < q ∧ q < 1 ∧ 1 ≤ K ∧
        ∀ n : ℕ, restrictedGrowth M S n ≤ K * q ^ n := by
  sorry

/-- C09. Symbolic cone bounds; the final lower factor is the genuinely reused
kernel-certified half. q, K and t are arbitrary real parameters. -/
theorem cone_numerical_bound (q K t : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht : t ≤ 1 / coneLoss q K ^ 2) :
    1 ≤ coneHeight q K ∧ 2 ≤ coneLoss q K ∧
    q * coneHeight q K + K = coneHeight q K - 1 ∧
    coneHeight q K - 1 + coneLoss q K * t ≤
      coneHeight q K * (1 - coneLoss q K * t) ∧
    localRadius ≤ 1 - coneLoss q K * t ∧
    0 < 1 - coneLoss q K * t := by
  sorry

/-- C10. The complete source Lemma 1. Only the fixed normalized reference is
product bounded; arbitrary perturbed N need not preserve its invariant flag. -/
theorem product_bounded_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hbounded : IsProductBounded M) (hradius : jointSpectralRadius M = 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        1 - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  sorry

/-- C11. A conservative all-length scalar estimate sufficient for the source
nonresonance argument. This eliminates a square-root computation; n=0 is kept. -/
theorem separated_sum_bound (n : ℕ) (x : Fin n → ℝ) (K F q : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hq0 : 0 < q) (hq1 : q < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hxK : ∀ i, x i ≤ K)
    (hpair : ∀ i j : Fin n, i ≠ j →
      x i * x j ≤ F * q ^ (max i.val j.val - min i.val j.val)) :
    ∑ i : Fin n, x i ≤ 2 * K + 4 * (F * q / (1 - q) ^ 2) + 1 := by
  sorry

/-- C12. Actual finite-block triangular radius formula, with no positivity
assumption on a diagonal radius and no independent choice of block generators. -/
theorem block_radius_formula {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius M =
      sSup (Set.range (fun i : Fin r => jointSpectralRadius (diagonalFamily b i M))) := by
  sorry

/-- C13. Full finite-block nonresonance theorem. The tensor families pair the
two diagonal blocks of the same A; grouped-prefix off-diagonal terms remain. -/
theorem block_nonresonance_product_bounded {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i M))
    (hpair : ∀ i j : Fin r, i ≠ j →
      jointSpectralRadius (pairedFamily M (blockMatrix b i) (blockMatrix b j)) < 1) :
    IsProductBounded M := by
  sorry

/-- C14. A substantive prerequisite to prove. No Barabanov/extremal norm or
product-boundedness assumption is permitted in this irreducible conclusion. -/
theorem irreducible_radius_one_product_bounded {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hirr : FamilyIrreducible M) (hradius : jointSpectralRadius M = 1) :
    IsProductBounded M := by
  sorry

/-- C15. Genuine finite invariant-flag construction. The blocks and change of
basis are conclusions, with a literal inverse pair and nonempty coordinate fibers. -/
theorem irreducible_flag {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d)) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ d ∧
      ∃ b : Fin d → Fin r, Function.Surjective b ∧
        ∃ Q R : Square d, Q * R = 1 ∧ R * Q = 1 ∧
          (∀ A ∈ conjugateFamily Q R M, IsUpperBlockTriangular b A) ∧
          ∀ i : Fin r, FamilyIrreducible (diagonalFamily b i (conjugateFamily Q R M)) := by
  sorry

/-- C16. Genuine similarity invariance of compact-family radius and product
boundedness; neither statement is encoded in `conjugateFamily`. -/
theorem similarity_semantics {d : ℕ} (hd : 1 ≤ d) (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) :
    IsCompact (conjugateFamily Q R M) ∧ (conjugateFamily Q R M).Nonempty ∧
    jointSpectralRadius (conjugateFamily Q R M) = jointSpectralRadius M ∧
    (IsProductBounded (conjugateFamily Q R M) ↔ IsProductBounded M) := by
  sorry

/-- C17. Actual exterior-basis dimensions, including degree zero. -/
theorem compound_dimensions (d k : ℕ) :
    compoundDim d k = Nat.choose d k ∧ (k ≤ d → 1 ≤ compoundDim d k) := by
  sorry

/-- C18. Exact identification with the pinned algebraic exterior-map API.
Sorted minors are not an arbitrary function merely assumed to behave like it. -/
theorem compound_coordinate_semantics {d : ℕ} (k : ℕ) (A : Square d)
    (i j : Fin (compoundDim d k)) :
    compoundMatrix k A i j =
      ((Pi.basisFun ℂ (Fin d)).exteriorPower k).repr
        (exteriorPower.map k (Matrix.toLin' A)
          (((Pi.basisFun ℂ (Fin d)).exteriorPower k) (compoundIndex d k j)))
        (compoundIndex d k i) := by
  sorry

/-- C19. Multiplicativity and the actual degree-zero scalar identity, with all
singular matrices and empty exterior bases retained. -/
theorem compound_algebra {d : ℕ} (k : ℕ) (A B : Square d) :
    compoundMatrix k (1 : Square d) = 1 ∧
    compoundMatrix k (A * B) = compoundMatrix k A * compoundMatrix k B ∧
    compoundMatrix 0 A = 1 := by
  sorry

/-- C20. Symbolic dimension-only norm bound. Its constant is outside the word
length exponent, so the radius comparison remains exact. -/
theorem compound_norm_bound {d : ℕ} (k : ℕ) (hk : k ≤ d) (A : Square d) :
    0 < compoundNormConstant d k ∧
    spectralNorm (compoundMatrix k A) ≤ compoundNormConstant d k * spectralNorm A ^ k := by
  sorry

/-- C21. All minors are locally Lipschitz, proved by symbolic telescoping and
determinant expansion, not by computing matrices or subdividing an interval. -/
theorem compound_local_lipschitz {d : ℕ} (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (L : ℝ) (hL : 0 < L) (A B : Square d)
    (hA : spectralNorm A ≤ L) (hB : spectralNorm B ≤ L) :
    0 < compoundLipschitzConstant d k L ∧
    spectralNorm (compoundMatrix k A - compoundMatrix k B) ≤
      compoundLipschitzConstant d k L * spectralNorm (A - B) := by
  sorry

/-- C22. Paired tensor multiplication uses the same chronological word. -/
theorem tensor_algebra {m n : ℕ} (A C : Square m) (B D : Square n) :
    tensorMatrix (1 : Square m) (1 : Square n) = 1 ∧
    tensorMatrix (A * C) (B * D) = tensorMatrix A B * tensorMatrix C D := by
  sorry

/-- C23. Conservative finite constants suffice in both directions, including
zero factors. No division by a matrix norm is required. -/
theorem tensor_norm_comparison {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Square m) (B : Square n) :
    spectralNorm (tensorMatrix A B) ≤
      (m : ℝ) * (n : ℝ) * spectralNorm A * spectralNorm B ∧
    spectralNorm A * spectralNorm B ≤
      (m : ℝ) * (n : ℝ) * spectralNorm (tensorMatrix A B) := by
  sorry

/-- C24. Literal fiber sizes sum to d, and every allocation is a positive
dimensional tensor space of degree at most d, even when some a_i are zero. -/
theorem allocation_dimensions {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :
    (∑ i : Fin r, blockDim b i) = d ∧
    allocationDegree b a ≤ d ∧ 1 ≤ allocationDim b a := by
  sorry

/-- C25. Diagonal blocks multiply as claimed only under actual triangularity;
that hypothesis is explicit. No independently chosen component word is substituted. -/
theorem allocation_algebra {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (A B : Square d) (hA : IsUpperBlockTriangular b A) (hB : IsUpperBlockTriangular b B) :
    allocationMatrix b a (1 : Square d) = 1 ∧
    allocationMatrix b a (A * B) = allocationMatrix b a A * allocationMatrix b a B := by
  sorry

/-- C26. Products of the literal allocation generators are bounded using
bounded diagonal families; all component words still share their original letters. -/
theorem allocation_product_bounded {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i M))
    (a : Allocation b) :
    IsProductBounded (allocationFamily b a M) := by
  sorry

/-- C27. Full exterior allocation-radius decomposition for actual triangular
matrices. Basis ordering and any sign/permutation changes must be proved. -/
theorem compound_allocation_radius {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) (k : ℕ) (hk : k ≤ d) :
    jointSpectralRadius (compoundFamily k M) =
      sSup (Set.range (fun a : DegreeAllocation b k =>
        jointSpectralRadius (allocationFamily b a.val M))) := by
  sorry

/-- C28. The higher degree in the nonresonance proof is strictly higher even
when coordinates tie. Pointwise max/min never leave the permitted block degrees. -/
theorem distinct_allocation_degrees {d r : ℕ} (b : Fin d → Fin r) (k : ℕ)
    (a c : DegreeAllocation b k) (hne : a ≠ c) :
    k < allocationDegree b (allocationMax a.val c.val) ∧
    allocationDegree b (allocationMin a.val c.val) < k := by
  sorry

/-- C29. A fixed word-independent constant permits reordering tensor norm
factors into max/min allocations. Vanishing factors and singular minors remain. -/
theorem allocation_tensor_norm_bridge {d r : ℕ} (b : Fin d → Fin r)
    (a c : Allocation b) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : Square d,
      spectralNorm (tensorMatrix (allocationMatrix b a P) (allocationMatrix b c P)) ≤
        D * spectralNorm (allocationMatrix b (allocationMax a c) P) *
          spectralNorm (allocationMatrix b (allocationMin a c) P) := by
  sorry

/-- C30. The strict higher-degree gap forces every distinct critical-degree
allocation pair to have radius below one. Same-generator pairing is explicit. -/
theorem critical_allocation_nonresonance {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i M))
    (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (hhigher : ∀ j : ℕ, k < j → j ≤ d → jointSpectralRadius (compoundFamily j M) < 1)
    (a c : DegreeAllocation b k) (hne : a ≠ c) :
    jointSpectralRadius
      (pairedFamily M (allocationMatrix b a.val) (allocationMatrix b c.val)) < 1 := by
  sorry

/-- C31. The actual exterior matrix family is product bounded when all its
allocation blocks and paired gaps satisfy the full finite-block hypotheses.
The required triangularization of the exterior representation must be proved. -/
theorem compound_nonresonance_product_bounded {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) (k : ℕ) (hk : k ≤ d)
    (halloc : ∀ a : DegreeAllocation b k, IsProductBounded (allocationFamily b a.val M))
    (hpair : ∀ a c : DegreeAllocation b k, a ≠ c →
      jointSpectralRadius
        (pairedFamily M (allocationMatrix b a.val) (allocationMatrix b c.val)) < 1) :
    IsProductBounded (compoundFamily k M) := by
  sorry

/-- C32. Genuine compact images and exact radius-power domination, including
degree zero and zero radius. Degree one retains the original radius exactly. -/
theorem compound_family_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) :
    (∀ k : ℕ, k ≤ d →
      IsCompact (compoundFamily k M) ∧ (compoundFamily k M).Nonempty ∧
      jointSpectralRadius (compoundFamily k M) ≤ jointSpectralRadius M ^ k) ∧
    jointSpectralRadius (compoundFamily 1 M) = jointSpectralRadius M := by
  sorry

/-- C33. Full source Lemma 5 for arbitrary compact normalized complex
families. Product boundedness and a maximal critical exterior degree are
conclusions; no irreducibility or original product-boundedness hypothesis occurs. -/
theorem critical_compound_product_bounded {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hradius : jointSpectralRadius M = 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧
      jointSpectralRadius (compoundFamily k M) = 1 ∧
      IsProductBounded (compoundFamily k M) ∧
      ∀ j : ℕ, k < j → j ≤ d → jointSpectralRadius (compoundFamily j M) < 1 := by
  sorry

/-- C34. Actual canonical Hausdorff distance of exterior images, using the
explicit local Lipschitz constant and both directions of the original sup-inf. -/
theorem compound_hausdorff_bound {d : ℕ} (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (M N : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hN : IsCompact N) (hneN : N.Nonempty) (L : ℝ) (hL : 0 < L)
    (hML : InNormBall M L) (hNL : InNormBall N L) :
    canonicalHausdorff (compoundFamily k M) (compoundFamily k N) ≤
      compoundLipschitzConstant d k L * canonicalHausdorff M N := by
  sorry

/-- C35. Positive homothety of the literal Hausdorff formula. No normalization
by a zero radius is allowed; that final case is handled separately. -/
theorem positive_hausdorff_scaling {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (c : ℝ) (hc : 0 < c) :
    canonicalHausdorff (scaledFamily c M) (scaledFamily c N) = c * canonicalHausdorff M N := by
  sorry

/-- C36. The final scalar transfer avoids fractional-power evaluation. -/
theorem root_lower_bound (k : ℕ) (hk : 1 ≤ k) (u z : ℝ)
    (hu : 0 ≤ u) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hz : z ≤ u ^ k) :
    z ≤ u := by
  sorry

/-- C37. Normalized full target, with unrestricted nonempty compact perturbed
families. The reference need not be product bounded or irreducible. -/
theorem normalized_pointwise_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hradius : jointSpectralRadius M = 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        1 - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  sorry

/-- C38. Complete unchanged MF-06: constants are chosen after the fixed M
and BEFORE N. All positive dimensions, infinite compact and reducible families,
zero/singular generators, zero radius and zero distance remain in scope. -/
theorem canonical_pointwise_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        jointSpectralRadius M - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  sorry

end NLA.MF06
