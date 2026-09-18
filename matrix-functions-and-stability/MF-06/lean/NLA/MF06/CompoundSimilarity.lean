/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Exterior functoriality transports the actual two-sided coordinate inverse.
The literal image families agree, so the already proved similarity result
applies to their genuine radii and all-word product bounds.
-/
import NLA.MF06.CompoundFirstDegree
import NLA.MF06.SimilaritySemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma compound_conjugateFamily {d : ℕ} (k : ℕ) (Q R : Square d) (M : Set (Square d)) :
    compoundFamily k (conjugateFamily Q R M) =
      conjugateFamily (compoundMatrix k Q) (compoundMatrix k R) (compoundFamily k M) := by
  unfold compoundFamily conjugateFamily
  rw [Set.image_image, Set.image_image]
  congr 1
  funext A
  exact ((compound_algebra k (R * A) Q).2.1).trans
    (congrArg (fun X => X * compoundMatrix k Q) (compound_algebra k R A).2.1)

lemma compound_similarity_semantics {d : ℕ} (hd : 1 ≤ d) (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (k : ℕ) (hk : k ≤ d) :
    jointSpectralRadius (compoundFamily k (conjugateFamily Q R M)) =
        jointSpectralRadius (compoundFamily k M) ∧
      (IsProductBounded (compoundFamily k (conjugateFamily Q R M)) ↔
        IsProductBounded (compoundFamily k M)) := by
  have hleft : compoundMatrix k Q * compoundMatrix k R = 1 := by
    rw [← (compound_algebra k Q R).2.1, hQR, (compound_algebra k 1 1).1]
  have hright : compoundMatrix k R * compoundMatrix k Q = 1 := by
    rw [← (compound_algebra k R Q).2.1, hRQ, (compound_algebra k 1 1).1]
  have hc := (compound_family_semantics hd M hM hneM).1 k hk
  rw [compound_conjugateFamily]
  exact (similarity_semantics ((compound_dimensions d k).2 hk)
    (compoundMatrix k Q) (compoundMatrix k R) hleft hright
    (compoundFamily k M) hc.1 hc.2.1).2.2

#print axioms compound_similarity_semantics
#assert_trust kernel compound_similarity_semantics

end NLA.MF06
