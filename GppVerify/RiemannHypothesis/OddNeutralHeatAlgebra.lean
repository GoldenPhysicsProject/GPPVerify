import Mathlib.Tactic

/-!
# Odd pole-neutral heat algebra

Finite algebra extracted from the odd-neutral heat reduction.  The differential
multiplier of T = D (D^2 - 1/4) in the bilateral-Laplace variable is

  m(z) = -z (z^2 - 1/4).

Pairing the reflected variables z and -z gives exactly

  m(z)m(-z) = α(α+1/4)^2,  α = -z^2.

This module proves only that algebra.  It does not formalize the explicit
formula, the zero sum, the deflation/tail argument, or RH.
-/

namespace GppOddNeutralHeat

/-- Laplace multiplier of the pole-neutral odd differential operator. -/
noncomputable def neutralMultiplier (z : ℂ) : ℂ :=
  -z * (z ^ 2 - (1 : ℂ) / 4)

/-- Squared-frequency heat exponent. -/
def heatAlpha (z : ℂ) : ℂ :=
  -(z ^ 2)

/-- Polynomial weight produced by the odd pole-neutral filter. -/
noncomputable def heatWeight (α : ℂ) : ℂ :=
  α * (α + (1 : ℂ) / 4) ^ 2

/-- The elementary pole channel z = +1/2 is killed exactly. -/
@[simp] theorem neutralMultiplier_half :
    neutralMultiplier ((1 : ℂ) / 2) = 0 := by
  norm_num [neutralMultiplier]

/-- The elementary pole channel z = -1/2 is killed exactly. -/
@[simp] theorem neutralMultiplier_neg_half :
    neutralMultiplier (-(1 : ℂ) / 2) = 0 := by
  norm_num [neutralMultiplier]

/-- The central channel z=0 is odd and is killed as well. -/
@[simp] theorem neutralMultiplier_zero :
    neutralMultiplier 0 = 0 := by
  simp [neutralMultiplier]

/-- Away from the central and elementary pole channels the multiplier is nonzero. -/
theorem neutralMultiplier_ne_zero {z : ℂ}
    (hz : z ≠ 0) (hpole : z ^ 2 ≠ (1 : ℂ) / 4) :
    neutralMultiplier z ≠ 0 := by
  unfold neutralMultiplier
  exact mul_ne_zero (neg_ne_zero.mpr hz) (sub_ne_zero.mpr hpole)

/-- The multiplier at the reflected point has the opposite first-order sign. -/
theorem neutralMultiplier_neg (z : ℂ) :
    neutralMultiplier (-z) = z * (z ^ 2 - (1 : ℂ) / 4) := by
  simp [neutralMultiplier]

/-- Exact heat-weight identity:
m(z)m(-z) = α(α+1/4)^2 with α=-z^2. -/
theorem reflected_multiplier_product (z : ℂ) :
    neutralMultiplier z * neutralMultiplier (-z) =
      heatWeight (heatAlpha z) := by
  simp [neutralMultiplier, heatAlpha, heatWeight]
  ring

/-- Expanded form of the same identity. -/
theorem reflected_multiplier_product_expanded (z : ℂ) :
    neutralMultiplier z * neutralMultiplier (-z) =
      -(z ^ 2) * (z ^ 2 - (1 : ℂ) / 4) ^ 2 := by
  rw [reflected_multiplier_product]
  simp only [heatWeight, heatAlpha]
  ring_nf

/-- The heat weight vanishes at α=0. -/
@[simp] theorem heatWeight_zero : heatWeight 0 = 0 := by
  simp [heatWeight]

/-- The heat weight also has the double elementary zero α=-1/4. -/
@[simp] theorem heatWeight_neg_quarter :
    heatWeight (-(1 : ℂ) / 4) = 0 := by
  norm_num [heatWeight]

end GppOddNeutralHeat

#print axioms GppOddNeutralHeat.neutralMultiplier_half
#print axioms GppOddNeutralHeat.neutralMultiplier_ne_zero
#print axioms GppOddNeutralHeat.reflected_multiplier_product
#print axioms GppOddNeutralHeat.heatWeight_neg_quarter
