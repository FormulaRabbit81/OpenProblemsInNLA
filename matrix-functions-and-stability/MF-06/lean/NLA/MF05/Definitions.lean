/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; statement draft, not a completed proof.

Original mathematical proof: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge, Theorem 2,
Proposition 5 and Corollary 7 of uniform_growth_and_holder.tex.

The actual matrix, word, norm and radius definitions and discounted word
envelope are reused unchanged from the published NLA.MF07 development.
Nothing here assumes a limit theorem, an extremal norm, or continuity of the
joint spectral radius. The independent Challenge supplies those obligations.
-/
import NLA.MF07.ProductEnvelope
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

noncomputable section
namespace NLA.MF05
open NLA.MF07

/-- Matrices act on the actual complex Euclidean space. Its continuous-linear
operator metric uses precisely the spectral norm, not an entrywise matrix norm. -/
def spectralImage {d : ℕ} (M : Set (Square d)) :
    Set (EuclideanVector d →L[ℂ] EuclideanVector d) :=
  (fun A : Square d => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A) '' M

/-- The literal infimum in the canonical spectral Hausdorff formula.
Nonempty compact families are required by all correspondence contracts. -/
def pointFamilyDistance {d : ℕ} (A : Square d) (N : Set (Square d)) : ℝ :=
  sInf ((fun B : Square d => spectralNorm (A - B)) '' N)

/-- The directed supremum in the canonical formula. -/
def directedSpectralDistance {d : ℕ} (M N : Set (Square d)) : ℝ :=
  sSup ((fun A : Square d => pointFamilyDistance A N) '' M)

/-- The original max-of-two-sup-inf formula, with the actual spectral norm. -/
def canonicalHausdorff {d : ℕ} (M N : Set (Square d)) : ℝ :=
  max (directedSpectralDistance M N) (directedSpectralDistance N M)

/-- Mathlib's Hausdorff distance of the spectral operator images. Its equality
with `canonicalHausdorff`, finiteness and nearest generators must be proved;
the library's total definition on empty/unbounded sets is never a hypothesis
substitute for nonempty compact families in the target. -/
def spectralHausdorff {d : ℕ} (M N : Set (Square d)) : ℝ :=
  Metric.hausdorffDist (spectralImage M) (spectralImage N)

/-- Scalar multiplication of every actual generator, with no radius condition. -/
def scaledFamily {d : ℕ} (c : ℝ) (M : Set (Square d)) : Set (Square d) :=
  (fun A : Square d => (c : ℂ) • A) '' M

/-- Adjoin the actual scalar identity. No radius formula is built into it. -/
def identityAdjoin {d : ℕ} (e : ℝ) (M : Set (Square d)) : Set (Square d) :=
  insert ((e : ℂ) • (1 : Square d)) M

/-- All generators lie in one spectral-norm ball; no cardinality restriction. -/
def InNormBall {d : ℕ} (M : Set (Square d)) (L : ℝ) : Prop :=
  ∀ A ∈ M, spectralNorm A ≤ L

def comparisonFactor (d : ℕ) (s : ℝ) : ℝ :=
  (d : ℝ) * s ^ (d - 1)

def comparisonRate (d : ℕ) (M : Set (Square d)) (L s : ℝ) : ℝ :=
  jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * L / s

/-- The concrete supremum of discounted word actions, with the empty word
included. Its finiteness, four complex norm axioms and generator bound are
conclusions of `controlled_comparison_norm`, not assumed structure fields. -/
def comparisonNorm (d : ℕ) (M : Set (Square d)) (L s : ℝ)
    (x : EuclideanVector d) : ℝ :=
  productEnvelope M (fun A => A) (comparisonRate d M L s) x

/-- The symbolic positive d-th-root scale used when 0 < delta ≤ L. -/
def holderScale (d : ℕ) (L delta : ℝ) : ℝ :=
  Real.rpow (L / delta) (1 / (d : ℝ))

/-- The manuscript's uniform, nonoptimal constant; d=1 remains included.
The sharper scalar Lipschitz constant and exponent sharpness are not targets. -/
def holderConstant (d : ℕ) (L : ℝ) : ℝ :=
  (d : ℝ) * (2 * (d : ℝ) + 1) * Real.rpow L (1 - 1 / (d : ℝ))

/-- The sole new fixed rational numerical certificate concerns this radius. -/
def localRadius : ℝ := 1 / 2

def localNormBound {d : ℕ} (M0 : Set (Square d)) : ℝ := familyNorm M0 + 1

end NLA.MF05
