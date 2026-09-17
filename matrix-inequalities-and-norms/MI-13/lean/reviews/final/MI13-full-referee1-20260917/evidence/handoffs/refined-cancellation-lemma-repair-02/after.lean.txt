/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Audenaert's refined commutator result
and the repository reduction retain their mathematical attribution.

Choose a top commutator eigenvector in the kernel of the SVD corner
functional, apply the cancelled estimate there, then use the spectral maximum.
-/
import NLA.MI13.CancelledSVD
import NLA.MI13.CommutatorMaximum
import NLA.MI13.SVD

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem refined_commutator_bound {r : ℕ} (hr : 2 ≤ r) (X Y : Square r) :
    frobeniusNorm (commutator X Y) ^ 2 ≤
      2 * (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) * frobeniusNorm Y ^ 2 := by
  obtain ⟨lam, E, hlam, hE, heig, hmax⟩ := commutator_spectral_maximum hr X
  by_cases hz : lam = 0
  · have hzero := hmax Y
    rw [hz, zero_mul] at hzero
    exact hzero.trans (mul_nonneg
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _))
  · have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hz)
    obtain ⟨U, V, hU, hV, hsvd⟩ := full_svd X
    obtain ⟨f, hf⟩ := svd_corner_functional X U V
    obtain ⟨Z, hZ, heigZ, hfZ⟩ := eigenspace_functional_kernel X E lam hpos hE heig f
    have hcorner := (hf Z).symm.trans hfZ
    have hcancel := cancelled_svd_bound hr X Z U V hU hV hsvd hcorner
    -- On the positive eigenspace the squared commutator norm is exactly
    -- the eigenvalue times the squared input norm, also for the new vector Z.
    have hpair := positive_eigenvector_pair X Z lam hpos hZ heigZ
    have henergy : frobeniusNorm (commutator X Z) ^ 2 = lam * frobeniusNorm Z ^ 2 := by
      rw [← (commutator_conjugate_symmetry X Z 0 0).2.2.2.2]
      exact hpair.2.2.2
    rw [henergy] at hcancel
    have hnZ : 0 < frobeniusNorm Z :=
      lt_of_le_of_ne (frobenius_semantics Z).2.2.1
        (Ne.symm (fun h => hZ ((frobenius_semantics Z).2.2.2.mp h)))
    have hlam_bound : lam ≤ 2 * (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) :=
      le_of_mul_le_mul_right hcancel (sq_pos_of_pos hnZ)
    exact (hmax Y).trans (mul_le_mul_of_nonneg_right hlam_bound (sq_nonneg _))

#print axioms refined_commutator_bound
#assert_trust kernel refined_commutator_bound

end
end NLA.MI13
