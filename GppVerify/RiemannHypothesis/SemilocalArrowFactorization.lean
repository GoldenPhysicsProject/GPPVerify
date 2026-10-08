import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Semilocal two-arrow factorization

This file formalizes two exact algebraic identities used in the semilocal Weil
matrix analysis.

1. The Nyquist-fold sine divided-difference kernel factors into the difference
   of two positive-band Gram channels.  Entrywise, the load-bearing trigonometric
   identity is

      (C_n C_m - S_n S_m) T_nm
        = (sin(c n) - sin(c m)) / (pi (n-m)),

   where
      C_n = cos(c n/2), S_n = sin(c n/2),
      T_nm = 2 sin(c(n-m)/2)/(pi(n-m)).

2. The elementary pole matrix is rank-two in the same (+,-) signature:
      L^2 - 16 pi^2 m n = L*L - (4 pi m)(4 pi n).

These are finite exact identities only.  They do not assert positivity of the
full prime--Archimedean Weil form and make no RH claim.
-/

open Real

namespace GppSemilocalArrowFactorization

/-- Off-diagonal Nyquist-fold two-arrow factorization. -/
theorem nyquist_two_arrow_offdiag
    (c n m : ℝ) (hnm : n ≠ m) :
    (Real.cos (c * n / 2) * Real.cos (c * m / 2)
        - Real.sin (c * n / 2) * Real.sin (c * m / 2))
      * (2 * Real.sin (c * (n - m) / 2) / (Real.pi * (n - m)))
      =
      (Real.sin (c * n) - Real.sin (c * m)) / (Real.pi * (n - m)) := by
  have hden : Real.pi * (n - m) ≠ 0 := by
    exact mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hnm)
  rw [← Real.cos_add]
  have htrig :
      2 * Real.cos (c * (n + m) / 2) * Real.sin (c * (n - m) / 2)
        = Real.sin (c * n) - Real.sin (c * m) := by
    rw [show c * n = c * (n + m) / 2 + c * (n - m) / 2 by ring,
        show c * m = c * (n + m) / 2 - c * (n - m) / 2 by ring,
        Real.sin_add, Real.sin_sub]
    ring
  have hcos :
      Real.cos (c * n / 2 + c * m / 2) = Real.cos (c * (n + m) / 2) := by
    congr 1 <;> ring
  rw [hcos]
  field_simp [hden]
  nlinarith [htrig]

/-- Diagonal Nyquist-fold two-arrow factorization. -/
theorem nyquist_two_arrow_diag (c n : ℝ) :
    (Real.cos (c * n / 2) ^ 2 - Real.sin (c * n / 2) ^ 2) * (c / Real.pi)
      = c * Real.cos (c * n) / Real.pi := by
  have h : Real.cos (c * n) = Real.cos (c * n / 2) ^ 2 - Real.sin (c * n / 2) ^ 2 := by
    rw [← Real.cos_two_mul']; congr 1; ring
  rw [h]; ring

/-- The numerator of the elementary pole block has the same (+,-) rank-two
signature as the Nyquist fold. -/
theorem pole_numerator_two_arrow (L m n : ℝ) :
    L ^ 2 - 16 * Real.pi ^ 2 * m * n
      = L * L - (4 * Real.pi * m) * (4 * Real.pi * n) := by
  ring

/-- Full entrywise rank-two factorization of the elementary pole block.
The hypotheses only ensure the displayed rational expressions are defined. -/
theorem pole_entry_two_arrow
    (L m n K : ℝ)
    (hm : L ^ 2 + 16 * Real.pi ^ 2 * m ^ 2 ≠ 0)
    (hn : L ^ 2 + 16 * Real.pi ^ 2 * n ^ 2 ≠ 0) :
    K * (L ^ 2 - 16 * Real.pi ^ 2 * m * n) /
        ((L ^ 2 + 16 * Real.pi ^ 2 * m ^ 2) *
         (L ^ 2 + 16 * Real.pi ^ 2 * n ^ 2))
      =
    K *
      ((L / (L ^ 2 + 16 * Real.pi ^ 2 * m ^ 2)) *
       (L / (L ^ 2 + 16 * Real.pi ^ 2 * n ^ 2))
       -
       ((4 * Real.pi * m) / (L ^ 2 + 16 * Real.pi ^ 2 * m ^ 2)) *
       ((4 * Real.pi * n) / (L ^ 2 + 16 * Real.pi ^ 2 * n ^ 2))) := by
  field_simp [hm, hn]
  ring



namespace CollisionMass

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- Regularized Archimedean collision/mass split. -/
theorem arch_collision_mass_split (rho r : ℝ) (I Ω : M) :
    -(rho • Ω) + (2 * r) • I
      = rho • ((2 : ℝ) • I - Ω) - (2 * (rho - r)) • I := by
  module

/-- Finite prime-power collision/mass split. -/
theorem finite_collision_mass_split
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ω : ι → M) (I : M) :
    -(∑ i, c i • Ω i)
      = (∑ i, c i • ((2 : ℝ) • I - Ω i)) - (2 * ∑ i, c i) • I := by
  have h : ∑ i, c i • ((2 : ℝ) • I - Ω i) = (2 * ∑ i, c i) • I - ∑ i, c i • Ω i := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, mul_comm (c _) (2 : ℝ), ← Finset.sum_smul,
      ← Finset.mul_sum]
  rw [h]; abel

end CollisionMass

end GppSemilocalArrowFactorization
