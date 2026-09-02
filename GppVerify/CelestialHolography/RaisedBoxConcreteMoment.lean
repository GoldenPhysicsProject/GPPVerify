import GppVerify.CelestialHolography.RaisedBoxPointwiseLimit
import GppVerify.CelestialHolography.RaisedBoxSimplexMajorantAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Concrete raised-box simplex moment

For Euclidean invariants `S,T > 0`, the raised massless scalar box in
`D = 8 - 2 epsilon` has the standard Feynman-parametric moment

  J_epsilon(S,T) = integral_{Delta_3} Q^{-epsilon},
  Q = S x1 x3 + T x2 x4,
  x4 = 1 - x1 - x2 - x3.

This file introduces that exact affine nested-interval object. The subsequent
measure layer will prove `J_epsilon -> 1/6` by dominated convergence using the
already-certified pointwise limit and one-channel majorant.
-/

namespace GppRaisedBoxConcreteMoment

open scoped Interval

/-- Fourth barycentric coordinate in affine coordinates on the standard
three-simplex. -/
def x4 (x1 x2 x3 : ℝ) : ℝ := 1 - x1 - x2 - x3

/-- Euclidean four-point Symanzik polynomial on the affine simplex. -/
def Q (S T x1 x2 x3 : ℝ) : ℝ :=
  S * x1 * x3 + T * x2 * x4 x1 x2 x3

/-- Raised-box Feynman-parametric integrand. -/
noncomputable def integrand (ε S T x1 x2 x3 : ℝ) : ℝ :=
  (Q S T x1 x2 x3) ^ (-ε : ℝ)

/-- Standard affine volume of the three-simplex, written in the same iterated
coordinates used by the physical Feynman parameter integral. -/
noncomputable def simplexVolume : ℝ :=
  ∫ x1 in (0 : ℝ)..1,
    ∫ x2 in (0 : ℝ)..(1 - x1),
      ∫ _x3 in (0 : ℝ)..(1 - x1 - x2), (1 : ℝ)

/-- Concrete raised-box simplex moment. -/
noncomputable def simplexMoment (ε S T : ℝ) : ℝ :=
  ∫ x1 in (0 : ℝ)..1,
    ∫ x2 in (0 : ℝ)..(1 - x1),
      ∫ x3 in (0 : ℝ)..(1 - x1 - x2), integrand ε S T x1 x2 x3

/-- At zero regulator the Feynman integrand is identically one, including the
boundary under Lean's totalized real-power convention. -/
@[simp] theorem integrand_zero (S T x1 x2 x3 : ℝ) :
    integrand 0 S T x1 x2 x3 = 1 := by
  simp [integrand]

/-- Therefore the zero-regulator moment is exactly the affine simplex volume. -/
theorem simplexMoment_zero (S T : ℝ) :
    simplexMoment 0 S T = simplexVolume := by
  simp [simplexMoment, simplexVolume, integrand]

/-- On a strictly interior simplex point with positive Euclidean invariants, the
Symanzik polynomial used here is exactly the positive quantity required by the
pointwise regulator theorem. -/
theorem Q_pos
    {S T x1 x2 x3 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hxsum : x1 + x2 + x3 < 1) :
    0 < Q S T x1 x2 x3 := by
  have hx4 : 0 < x4 x1 x2 x3 := by
    unfold x4
    linarith
  unfold Q
  positivity

/-- Pointwise regulator removal at every strictly interior simplex point. -/
theorem integrand_tendsto_one
    {S T x1 x2 x3 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hxsum : x1 + x2 + x3 < 1) :
    Filter.Tendsto
      (fun ε : ℝ => integrand ε S T x1 x2 x3)
      (nhds 0) (nhds 1) := by
  unfold integrand
  exact GppRaisedBoxPointwiseLimit.tendsto_neg_rpow_one
    (Q_pos hS hT hx1 hx2 hx3 hxsum)

/-- The abstract one-channel estimate specializes exactly to the concrete
Feynman-parametric integrand on the affine simplex. -/
theorem integrand_le_one_channel_majorant
    {ε δ S T x1 x2 x3 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx3 : 0 < x3)
    (hxsum : x1 + x2 + x3 ≤ 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ) (hδ : 0 < δ) :
    integrand ε S T x1 x2 x3 ≤
      1 + (S * x1 * x3) ^ (-δ : ℝ) := by
  have hx4 : 0 ≤ x4 x1 x2 x3 := by
    unfold x4
    linarith
  unfold integrand Q
  exact GppRaisedBoxSimplexMajorantAlgebra.symanzik_neg_eps_majorized
    hS hT.le hx1 hx2 hx3 hx4 hε0 hεδ hδ

end GppRaisedBoxConcreteMoment

#print axioms GppRaisedBoxConcreteMoment.simplexMoment_zero
#print axioms GppRaisedBoxConcreteMoment.Q_pos
#print axioms GppRaisedBoxConcreteMoment.integrand_tendsto_one
#print axioms GppRaisedBoxConcreteMoment.integrand_le_one_channel_majorant
