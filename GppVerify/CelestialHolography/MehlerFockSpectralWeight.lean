import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Mehler-Fock / Wiener-Hopf spectral weight algebra

This file records the exact elementary hyperbolic-weight relation discovered in
`GPPDiscovery2`. The Gamma-function interpretation is deliberately left outside
the formal statement until the required Gamma-modulus API is formalized.
-/

namespace GppMehlerFockSpectral

open Real

/-- Wiener-Hopf spectral weight. -/
noncomputable def wienerHopfWeight (lam : ℝ) : ℝ :=
  Real.pi * lam / Real.sinh (Real.pi * lam)

/-- Mehler-Fock density in explicit sinh/cosh form. -/
noncomputable def mehlerFockWeight (lam : ℝ) : ℝ :=
  lam * Real.sinh (Real.pi * lam) / Real.cosh (Real.pi * lam)

/-- The collapsed product density obtained after multiplying the Wiener-Hopf
and Mehler-Fock factors. Discovery identifies this also with
`lam² |Γ(1/2 + i lam)|²`; only the elementary hyperbolic form is used here. -/
noncomputable def collapsedWeight (lam : ℝ) : ℝ :=
  Real.pi * lam ^ 2 / Real.cosh (Real.pi * lam)

/-- The product of the two weights collapses to the half-shifted hyperbolic factor. -/
theorem weight_product {lam : ℝ}
    (hs : Real.sinh (Real.pi * lam) ≠ 0)
    (hc : Real.cosh (Real.pi * lam) ≠ 0) :
    wienerHopfWeight lam * mehlerFockWeight lam = collapsedWeight lam := by
  unfold wienerHopfWeight mehlerFockWeight collapsedWeight
  field_simp [hs, hc]
  ring

/-- The collapsed spectral density is pointwise nonnegative. -/
theorem collapsedWeight_nonneg (lam : ℝ) :
    0 ≤ collapsedWeight lam := by
  unfold collapsedWeight
  exact div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg lam)) (Real.cosh_pos _).le

/-- Away from the origin the collapsed density is strictly positive. -/
theorem collapsedWeight_pos {lam : ℝ} (hlam : lam ≠ 0) :
    0 < collapsedWeight lam := by
  unfold collapsedWeight
  exact div_pos (mul_pos Real.pi_pos (sq_pos_of_ne_zero hlam)) (Real.cosh_pos _)

/-- Both explicitly defined weights vanish at the origin under Lean's totalized division. -/
theorem mehlerFockWeight_zero : mehlerFockWeight 0 = 0 := by
  simp [mehlerFockWeight]

/-- The collapsed density vanishes at the origin. -/
theorem collapsedWeight_zero : collapsedWeight 0 = 0 := by
  simp [collapsedWeight]

/-- The collapsed density is an even spectral weight. -/
theorem collapsedWeight_neg (lam : ℝ) : collapsedWeight (-lam) = collapsedWeight lam := by
  unfold collapsedWeight
  have harg : Real.pi * (-lam) = -(Real.pi * lam) := by ring
  rw [harg, Real.cosh_neg]
  ring

/-- The origin is the exact zero set of the collapsed density. -/
theorem collapsedWeight_eq_zero_iff (lam : ℝ) :
    collapsedWeight lam = 0 ↔ lam = 0 := by
  constructor
  · intro h
    by_contra hlam
    exact (ne_of_gt (collapsedWeight_pos hlam)) h
  · intro hlam
    subst lam
    exact collapsedWeight_zero

end GppMehlerFockSpectral

#print axioms GppMehlerFockSpectral.weight_product
#print axioms GppMehlerFockSpectral.collapsedWeight_nonneg
#print axioms GppMehlerFockSpectral.collapsedWeight_pos
#print axioms GppMehlerFockSpectral.collapsedWeight_neg
#print axioms GppMehlerFockSpectral.collapsedWeight_eq_zero_iff
