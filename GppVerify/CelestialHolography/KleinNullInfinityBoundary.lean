import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbientFourDualitySpine
import GppVerify.CelestialHolography.KleinSpinorIncidence

/-!
# Null infinity as a tangent hyperplane section of the Klein quadric

For flat conformal twistor geometry, a simple/null infinity twistor determines a point
`I` on the Klein quadric.  The conformal boundary is the hyperplane section

  Q_Klein ∩ I^perp,

where orthogonality is taken with the epsilon-induced Klein bilinear form.  Because `I`
is itself null, `I^perp` is the tangent hyperplane to the quadric at `I`.

In the Plucker chart used throughout GPPVerify we choose

  I = e2 ∧ e3 = (0,0,0,0,0,1).

Then the epsilon pairing with `I` is simply `p01`.  Consequently

  finite big cell:  p01 != 0, normalized to p01 = 1,
  conformal boundary: p01 = 0.

This gives a direct algebraic meaning to the fact that `chartPlucker(A)` covers only the
finite affine region: every such point has `p01=1` and therefore lies off the boundary.

The module proves only this flat/Klein compactification statement.  It does not identify a
black-hole event horizon with null infinity.
-/

namespace GppKleinNullInfinityBoundary

open GppGrassmannianGooglyDecomposition
open GppAmbientFourDualitySpine
open GppKleinSpinorIncidence
open GppTwistorAnnihilatorIncidence

/-- Standard flat infinity point in the chosen Plucker coordinates. -/
def infinityPoint : P6 := ⟨0,0,0,0,0,1⟩

/-- The flat infinity point lies on the Klein quadric. -/
theorem infinityPoint_is_null : kleinQ infinityPoint = 0 := by
  norm_num [infinityPoint, kleinQ]

/-- Epsilon/Klein pairing with the infinity point extracts the affine Plucker coordinate
`p01`. -/
theorem epsilonPair_infinityPoint (p : P6) :
    epsilonPair infinityPoint p = p.p01 := by
  simp [epsilonPair, infinityPoint]

/-- By symmetry the same is true with the arguments reversed. -/
theorem epsilonPair_to_infinityPoint (p : P6) :
    epsilonPair p infinityPoint = p.p01 := by
  rw [epsilonPair_symm]
  exact epsilonPair_infinityPoint p

/-- The tangent hyperplane condition at the null infinity point. -/
def OnInfinityHyperplane (p : P6) : Prop :=
  epsilonPair infinityPoint p = 0

/-- In this chart, the tangent hyperplane is exactly `p01=0`. -/
theorem onInfinityHyperplane_iff_p01_zero (p : P6) :
    OnInfinityHyperplane p ↔ p.p01 = 0 := by
  simp [OnInfinityHyperplane, epsilonPair_infinityPoint]

/-- The infinity point itself lies in its tangent hyperplane, as expected for a null point. -/
theorem infinityPoint_on_own_tangent : OnInfinityHyperplane infinityPoint := by
  simp [OnInfinityHyperplane, epsilonPair_infinityPoint, infinityPoint]

/-- Algebraic model of the conformal null boundary: a Klein-null point lying in the
tangent hyperplane of `infinityPoint`. -/
def OnConformalInfinity (p : P6) : Prop :=
  kleinQ p = 0 ∧ OnInfinityHyperplane p

/-- Coordinate characterization of the flat conformal boundary. -/
theorem onConformalInfinity_iff (p : P6) :
    OnConformalInfinity p ↔ kleinQ p = 0 ∧ p.p01 = 0 := by
  simp [OnConformalInfinity, onInfinityHyperplane_iff_p01_zero]

/-- Every graph-chart point has affine coordinate `p01=1`. -/
theorem chartPlucker_p01 (A : M2) : (chartPlucker A).p01 = 1 := by
  rfl

/-- Therefore no point of the normalized finite graph chart lies on the infinity
hyperplane. -/
theorem graph_chart_off_infinity_hyperplane (A : M2) :
    ¬ OnInfinityHyperplane (chartPlucker A) := by
  rw [onInfinityHyperplane_iff_p01_zero]
  norm_num [chartPlucker]

/-- In particular the finite graph chart and conformal null boundary are disjoint. -/
theorem graph_chart_off_conformal_infinity (A : M2) :
    ¬ OnConformalInfinity (chartPlucker A) := by
  intro h
  exact graph_chart_off_infinity_hyperplane A h.2

/-- The standard infinity point is itself a conformal-boundary point. -/
theorem infinityPoint_on_conformal_infinity :
    OnConformalInfinity infinityPoint := by
  exact ⟨infinityPoint_is_null, infinityPoint_on_own_tangent⟩

/-- The infinity twistor's epsilon Clifford action has kernel equal to its ordinary
twistor line: the last two coordinate directions. -/
theorem infinity_cPlus_kernel (z : V4) :
    cPlus infinityPoint z = (0,0,0,0) ↔ z.1 = 0 ∧ z.2.1 = 0 := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [cPlus, infinityPoint]

/-- On the dual chirality the kernel is the complementary first two coordinate directions. -/
theorem infinity_cMinus_kernel (α : V4) :
    cMinus infinityPoint α = (0,0,0,0) ↔ α.2.2.1 = 0 ∧ α.2.2.2 = 0 := by
  rcases α with ⟨a0,a1,a2,a3⟩
  simp [cMinus, infinityPoint]

/-- The flat infinity point has zero Klein bridge parameter and therefore gives a
nilpotent, not invertible, chirality-coupling operator. -/
theorem infinity_clifford_square_zero (ψ : DiracTwistor) :
    cliffordAction infinityPoint (cliffordAction infinityPoint ψ) =
      ((0,0,0,0),(0,0,0,0)) := by
  rw [cliffordAction_sq, infinityPoint_is_null]
  rcases ψ with ⟨z,α⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  rcases α with ⟨a0,a1,a2,a3⟩
  simp [scale4]

end GppKleinNullInfinityBoundary
