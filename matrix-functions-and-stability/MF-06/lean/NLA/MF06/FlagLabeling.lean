/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Each actual basis vector is labeled by its first nonzero flag level. A strict
flag forces every label to occur, and every prefix is exactly the span of
lower labels. No ordering of the chosen basis is assumed.
-/
import NLA.MF06.AdaptedBasis

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma basis_chain_labeling {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (hF : StrictMono F) (h0 : F 0 = ⊥) (htop : F (Fin.last r) = ⊤)
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d))
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | B j ∈ F i}) = F i) :
    ∃ b : Fin d → Fin r, Function.Surjective b ∧
      (∀ j i, B j ∈ F i ↔ (b j).val < i.val) ∧
      ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i := by
  classical
  let index (n : ℕ) : Fin (r + 1) := ⟨min n r, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let G (n : ℕ) := F (index n)
  have hindex : Monotone index := fun _ _ h => min_le_min_right r h
  have hG : Monotone G := hF.monotone.comp hindex
  have hindexi (i : Fin (r + 1)) : index i.val = i := by
    ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  have hg0 : G 0 = ⊥ := by
    change F (index 0) = ⊥
    have hi : index 0 = 0 := by ext; simp [index]
    rw [hi, h0]
  have hgr : G r = ⊤ := by
    change F (index r) = ⊤
    have hi : index r = Fin.last r := by ext; simp [index]
    rw [hi, htop]
  have hlast (j : Fin d) : B j ∈ G r := by rw [hgr]; exact Submodule.mem_top
  have hex (j : Fin d) : ∃ n : ℕ, B j ∈ G n := ⟨r, hlast j⟩
  let level (j : Fin d) := Nat.find (hex j)
  have hpos (j : Fin d) : 0 < level j := by
    apply (Nat.find_pos (hex j)).mpr
    rw [hg0]
    exact B.ne_zero j
  have hle (j : Fin d) : level j ≤ r := Nat.find_min' (hex j) (hlast j)
  let b (j : Fin d) : Fin r := ⟨level j - 1, by have := hpos j; have := hle j; omega⟩
  have hcriterion (j : Fin d) (i : Fin (r + 1)) : B j ∈ F i ↔ (b j).val < i.val := by
    change B j ∈ F i ↔ level j - 1 < i.val
    constructor
    · intro hj
      have hji : B j ∈ G i.val := by change B j ∈ F (index i.val); rwa [hindexi i]
      have hm : level j ≤ i.val := Nat.find_min' (hex j) hji
      have hp : 0 < level j := hpos j
      omega
    · intro hji
      have hli : level j ≤ i.val := by have := hpos j; omega
      have hmem : B j ∈ G (level j) := Nat.find_spec (hex j)
      have hresult := hG hli hmem
      change B j ∈ F (index i.val) at hresult
      rwa [hindexi i] at hresult
  have hsurj : Function.Surjective b := by
    intro i
    by_contra hn
    have hne (j : Fin d) : b j ≠ i := fun h => hn ⟨j, h⟩
    have hback : F i.succ ≤ F i.castSucc := by
      rw [← hspan i.succ]
      apply Submodule.span_le.mpr
      rintro x ⟨j, hj, rfl⟩
      apply (hcriterion j i.castSucc).mpr
      have hupper := (hcriterion j i.succ).mp hj
      have hval : (b j).val ≠ i.val := fun h => hne j (Fin.ext h)
      change (b j).val < i.val + 1 at hupper
      change (b j).val < i.val
      omega
    exact (hF i.castSucc_lt_succ).not_ge hback
  refine ⟨b, hsurj, hcriterion, ?_⟩
  intro i
  have hsets : {j | (b j).val < i.val} = {j | B j ∈ F i} := by
    ext j
    exact (hcriterion j i).symm
  rw [hsets, hspan i]

#print axioms basis_chain_labeling
#assert_trust kernel basis_chain_labeling

end NLA.MF06
