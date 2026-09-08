import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbitwistorSturmBidegrees

/-!
# Reciprocal factor exchange and the Sturm potential

This module isolates another exact finite-algebra consequence of the ambidextrous
Penrose-ray Sturm carrier.

There are two distinct reciprocal operations in the current geometry:

1. swapping the two independent spinor rescaling factors `(r,s)` exchanges the two
   bidegrees and sends an anti-diagonal parameter `(a,a⁻¹)` to `(a⁻¹,a)`;
2. swapping the two Sturm components `(x,p)` conjugates the projective Sturm generator
   at nonzero potential `U` to the generator at reciprocal potential `U⁻¹`, up to the
   overall scalar `-U`.

The second identity is

    J G_U J = (-U) G_{U⁻¹},

for `J(x,p)=(p,x)` and `G_U(x,p)=(p,-Ux)`.  Since an overall nonzero scalar is irrelevant
to the induced projective line field after the corresponding reparametrization, this is a
literal reciprocal-potential symmetry of the finite rank-two system.

Semantic boundary: this is NOT yet a theorem that `U=P(k,k)` is the positive Haar scale,
nor that Sturm component exchange is the physical celestial shadow.  It sharpens the
bridge problem by showing exactly what such an identification would have to transport.
-/

namespace GppSturmReciprocalPotential

open GppAmbidextrousPenroseRayQuotients
open GppAmbitwistorSturmBidegrees

/-- Swap the two independent spinor-rescaling factors. -/
def swapFactors (r s : ℂ) : ℂ × ℂ := (s,r)

/-- On the anti-diagonal torus, factor exchange is parameter inversion. -/
theorem swapFactors_antidiagonal (a : ℂ) :
    swapFactors a a⁻¹ = (a⁻¹,a) := by
  rfl

/-- Factor exchange leaves the physical tangent/derivative scale `rs` unchanged. -/
theorem derivativeScale_factorSwap (r s : ℂ) :
    derivativeScale s r = derivativeScale r s := by
  simp [derivativeScale, mul_comm]

/-- It likewise leaves the curvature homogeneity factor `(rs)^2` unchanged. -/
theorem curvatureScale_factorSwap (r s U : ℂ) :
    curvatureScale s r U = curvatureScale r s U := by
  simp [curvatureScale, mul_comm]

/-- Exchange the two integer homogeneity slots. -/
def swapBiWeight (w : BiWeight) : BiWeight := (w.2,w.1)

/-- The complete left/right bidegree package is exchanged slot-for-slot. -/
theorem factorSwap_exchanges_left_right_weights :
    swapBiWeight leftFieldWeight = rightFieldWeight ∧
    swapBiWeight leftMomentumWeight = rightMomentumWeight ∧
    swapBiWeight leftEquationWeight = rightEquationWeight ∧
    swapBiWeight tangentWeight = tangentWeight ∧
    swapBiWeight curvatureWeight = curvatureWeight := by
  norm_num [swapBiWeight, leftFieldWeight, rightFieldWeight,
    leftMomentumWeight, rightMomentumWeight, leftEquationWeight, rightEquationWeight,
    tangentWeight, curvatureWeight]

/-- **Reciprocal-potential conjugacy.**  For nonzero `U`, Sturm component exchange sends
`G_U` to `G_{U⁻¹}` up to the common scalar `-U`:

`J G_U J = (-U) G_{U⁻¹}`.
-/
theorem reciprocalSwap_conjugates_sturm_to_inverse
    (U : ℂ) (hU : U ≠ 0) (u : SturmState) :
    reciprocalSwap (sturmGenerator U (reciprocalSwap u)) =
      scaleSturmState (-U) (sturmGenerator U⁻¹ u) := by
  rcases u with ⟨x,p⟩
  have hUi : U * U⁻¹ = 1 := mul_inv_cancel₀ hU
  simp [reciprocalSwap, sturmGenerator, scaleSturmState, hUi]

/-- The reciprocal potential operation is involutive at the parameter level. -/
theorem reciprocal_potential_involution (U : ℂ) :
    (U⁻¹)⁻¹ = U := by
  simp

end GppSturmReciprocalPotential
