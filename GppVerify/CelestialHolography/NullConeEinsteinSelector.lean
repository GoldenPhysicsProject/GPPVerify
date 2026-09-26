import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Null-cone rigidity behind the ambitwistor Einstein selector

In split signature a tangent vector may be represented by a real `2x2` matrix

  X = [[a,b],[c,d]],

with conformal quadratic form proportional to

  q(X)=det X = a*d-b*c.

The null cone is therefore exactly the rank-one locus `det X=0`.

The almost-Einstein equation for a scale `sigma` may be written

  (nabla_a nabla_b sigma + P_ab sigma)_0 = 0.

Contracting with a null tangent `k` removes the pure-trace part, and along an affine null
geodesic gives the scalar ODE

  sigma'' + P(k,k) sigma = 0.

Conversely, if this scalar null-direction equation holds for every null direction, then
the symmetric tensor

  T_ab = nabla_a nabla_b sigma + P_ab sigma

has `T(k,k)=0` on the whole null cone.  The theorem below proves the required split
linear-algebra rigidity: every real quadratic form on `M_2(R)` which vanishes on all
rank-one matrices is a scalar multiple of the determinant.  Therefore its trace-free
part is zero.

This file formalizes the exact algebraic converse.  The differential-geometric passage
from the almost-Einstein PDE to the null-geodesic ODE is standard external geometry and
is not encoded in the finite coordinate carrier here.
-/

namespace GppNullConeEinsteinSelector

open GppGrassmannianGooglyDecomposition

/-- General real quadratic form in four coordinates, with cross-term coefficients already
absorbing the conventional factors of two of a symmetric bilinear form. -/
def quad4
    (A B C D E F G H I J : ℝ) (a b c d : ℝ) : ℝ :=
  A*a*a + B*b*b + C*c*c + D*d*d +
  E*a*b + F*a*c + G*a*d + H*b*c + I*b*d + J*c*d

/-- Split null-cone rigidity: if a quadratic form vanishes on every `2x2` matrix of
zero determinant, then it is a scalar multiple of the determinant quadratic form. -/
theorem vanishing_on_rankOne_implies_det_multiple
    (A B C D E F G H I J : ℝ)
    (hnull : ∀ a b c d : ℝ,
      det2 (a,b,c,d) = 0 -> quad4 A B C D E F G H I J a b c d = 0) :
    ∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d) := by
  have hA := hnull 1 0 0 0 (by norm_num [det2])
  have hB := hnull 0 1 0 0 (by norm_num [det2])
  have hC := hnull 0 0 1 0 (by norm_num [det2])
  have hD := hnull 0 0 0 1 (by norm_num [det2])
  simp [quad4] at hA hB hC hD
  have hE := hnull 1 1 0 0 (by norm_num [det2])
  have hF := hnull 1 0 1 0 (by norm_num [det2])
  have hI := hnull 0 1 0 1 (by norm_num [det2])
  have hJ := hnull 0 0 1 1 (by norm_num [det2])
  simp [quad4, hA, hB, hC, hD] at hE hF hI hJ
  have hGH := hnull 1 1 1 1 (by norm_num [det2])
  simp [quad4, hA, hB, hC, hD, hE, hF, hI, hJ] at hGH
  have hH : H = -G := by linarith
  refine ⟨G, ?_⟩
  intro a b c d
  simp [quad4, hA, hB, hC, hD, hE, hF, hI, hJ, hH, det2]
  ring

/-- Converse: every scalar multiple of the split determinant vanishes on the null cone. -/
theorem det_multiple_vanishes_on_rankOne
    (mu a b c d : ℝ) (hdet : det2 (a,b,c,d) = 0) :
    mu * det2 (a,b,c,d) = 0 := by
  rw [hdet]
  ring

/-- Exact iff formulation: vanishing on the full split null cone is equivalent to being
pure trace, represented here by a scalar multiple of the determinant metric quadratic. -/
theorem null_cone_vanishing_iff_det_multiple
    (A B C D E F G H I J : ℝ) :
    (∀ a b c d : ℝ,
      det2 (a,b,c,d) = 0 -> quad4 A B C D E F G H I J a b c d = 0) ↔
    (∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d)) := by
  constructor
  · exact vanishing_on_rankOne_implies_det_multiple A B C D E F G H I J
  · rintro ⟨mu,hmu⟩ a b c d hdet
    rw [hmu a b c d, hdet]
    ring

end GppNullConeEinsteinSelector
