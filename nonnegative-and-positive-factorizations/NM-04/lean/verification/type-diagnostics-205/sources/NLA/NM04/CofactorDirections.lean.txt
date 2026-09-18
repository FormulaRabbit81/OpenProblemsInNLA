/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Symbolic direction expansion used in
Colbrook's NM-04 balanced-minor argument; no inverses or nonempty assumptions.
-/
import NLA.NM04.MinorLinearity
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped Matrix
universe u v w

theorem cofactorForm_outer_sub {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (u : α → 𝕜) (v : β → 𝕜) (a : 𝕜) :
    cofactorForm T I (Matrix.vecMulVec (fun i => 1 - u i) (fun j => 1 - a * v j)) =
      cofactorForm T I (fun _ _ => 1) -
        cofactorForm T I (Matrix.vecMulVec u (fun _ => 1)) -
        a * cofactorForm T I (Matrix.vecMulVec (fun _ => 1) v) +
        a * cofactorForm T I (Matrix.vecMulVec u v) := by
  have hdir : Matrix.vecMulVec (fun i => 1 - u i) (fun j => 1 - a * v j) =
      Matrix.of (fun (_ : α) (_ : β) => (1 : 𝕜)) +
        (-1 : 𝕜) • Matrix.vecMulVec u (fun _ => 1) +
        (-a) • Matrix.vecMulVec (fun _ => 1) v + a • Matrix.vecMulVec u v := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    ring
  rw [hdir]
  simp only [cofactorForm_add, cofactorForm_smul]
  have hone : Matrix.of (fun (_ : α) (_ : β) => (1 : 𝕜)) = (fun _ _ => 1) := rfl
  rw [hone]
  ring

#print axioms cofactorForm_outer_sub
#assert_trust kernel cofactorForm_outer_sub

end
end NLA.NM04
