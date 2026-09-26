import Mathlib.Tactic

/-!
# Supercritical dimension-shift coefficient algebra

For `r = n - 2 + m`, the leading zero of `Gamma(r-eps)/Gamma(-eps)` and the
pole of `Gamma(-m+eps)` combine to the scalar coefficient

  `(-1)^(m+1) * (r-1)! / m!`.

The analytic Gamma asymptotics and Feynman-simplex moment are separate targets;
this file records the exact factorial algebra linking the critical and gravity cases.
-/

namespace GppSupercriticalDimensionShiftAlgebra

/-- Universal zero-times-pole coefficient, as a rational number. -/
def supercriticalCoeff (r m : ℕ) : ℚ :=
  (-1 : ℚ) ^ (m + 1) * (Nat.factorial (r - 1) : ℚ) /
    (Nat.factorial m : ℚ)

/-- The four-graviton `mu^8` box has `r=4`, `m=2`, hence coefficient `-3`. -/
theorem gravity_mu8_box_coeff : supercriticalCoeff 4 2 = -3 := by
  norm_num [supercriticalCoeff, Nat.factorial]

/-- The critical family is the `m=0` specialization. -/
theorem critical_coeff (r : ℕ) :
    supercriticalCoeff r 0 = -(Nat.factorial (r - 1) : ℚ) := by
  simp [supercriticalCoeff]

/-- For `n>=3`, the critical `r=n-2` coefficient is `-(n-3)!`. -/
theorem critical_ngon_coeff {n : ℕ} (hn : 3 ≤ n) :
    supercriticalCoeff (n - 2) 0 = -(Nat.factorial (n - 3) : ℚ) := by
  rw [critical_coeff]
  congr 2
  congr 1
  omega

end GppSupercriticalDimensionShiftAlgebra

#print axioms GppSupercriticalDimensionShiftAlgebra.gravity_mu8_box_coeff
#print axioms GppSupercriticalDimensionShiftAlgebra.critical_ngon_coeff
