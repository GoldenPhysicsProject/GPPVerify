import GppVerify.CelestialHolography.ScalarBoxLogScaleBounds
import GppVerify.CelestialHolography.ScalarBoxPoleLogScaleBounds
import Mathlib.Tactic

/-!
# Scalar-box logarithmic square remainder

The regulated scalar-box endpoint analysis supplies quantitative replacements

  log a = log(m/U) + O(Ea),
  log t = log(m/S) + O(Et).

This file isolates the elementary algebra needed to propagate those first-order
logarithmic errors through the squared logarithms appearing after the reciprocal
dilogarithm identity.  The resulting bound is explicit and is the bridge to the
final `m log^2 m -> 0` regulator remainder.
-/

namespace GppScalarBoxLogSquareRemainder

/-- Certified lower-endpoint logarithmic error scale. -/
noncomputable def lowerLogError (δ η : ℝ) : ℝ :=
  (289 / 192 : ℝ) * (η + (33 / 64 : ℝ) * δ)

/-- Certified pole-endpoint logarithmic error scale. -/
noncomputable def poleLogError (δ η : ℝ) : ℝ :=
  (103 / 68 : ℝ) * δ + (1 / 3 : ℝ) * (δ * η) + (4 / 3 : ℝ) * η

/-- Both certified error scales are nonnegative on the physical chamber. -/
theorem logError_nonneg
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    0 ≤ lowerLogError δ η ∧ 0 ≤ poleLogError δ η := by
  unfold lowerLogError poleLogError
  constructor <;> positivity

/-- If `x` differs from `y` by at most `E`, then their squares differ by at most
`E * (2 * |y| + E)`. -/
theorem abs_sq_sub_sq_le_of_abs_sub_le
    {x y E : ℝ}
    (hE : 0 ≤ E)
    (hxy : |x - y| ≤ E) :
    |x ^ 2 - y ^ 2| ≤ E * (2 * |y| + E) := by
  have hsum : |x + y| ≤ E + 2 * |y| := by
    calc
      |x + y| = |(x - y) + 2 * y| := by
        congr 1
        ring
      _ ≤ |x - y| + |2 * y| := abs_add _ _
      _ = |x - y| + 2 * |y| := by
        rw [abs_mul]
        norm_num
      _ ≤ E + 2 * |y| := add_le_add_right hxy _
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
  calc
    |x - y| * |x + y| ≤ E * |x + y| :=
      mul_le_mul_of_nonneg_right hxy (abs_nonneg _)
    _ ≤ E * (E + 2 * |y|) :=
      mul_le_mul_of_nonneg_left hsum hE
    _ = E * (2 * |y| + E) := by ring

/-- Replacing both moving logarithms by their natural regulator scales produces
an explicit sum of first-order square errors. -/
theorem abs_log_square_pair_remainder_le
    {a t m S U Ea Et : ℝ}
    (hEa : 0 ≤ Ea) (hEt : 0 ≤ Et)
    (ha : |Real.log a - Real.log (m / U)| ≤ Ea)
    (ht : |Real.log t - Real.log (m / S)| ≤ Et) :
    |((Real.log a) ^ 2 - (Real.log t) ^ 2) -
      ((Real.log (m / U)) ^ 2 - (Real.log (m / S)) ^ 2)| ≤
      Ea * (2 * |Real.log (m / U)| + Ea) +
      Et * (2 * |Real.log (m / S)| + Et) := by
  have ha2 := abs_sq_sub_sq_le_of_abs_sub_le hEa ha
  have ht2 := abs_sq_sub_sq_le_of_abs_sub_le hEt ht
  have htri :
      |((Real.log a) ^ 2 - (Real.log (m / U)) ^ 2) -
        ((Real.log t) ^ 2 - (Real.log (m / S)) ^ 2)| ≤
      |(Real.log a) ^ 2 - (Real.log (m / U)) ^ 2| +
      |(Real.log t) ^ 2 - (Real.log (m / S)) ^ 2| :=
    abs_sub _ _
  calc
    |((Real.log a) ^ 2 - (Real.log t) ^ 2) -
      ((Real.log (m / U)) ^ 2 - (Real.log (m / S)) ^ 2)| =
      |((Real.log a) ^ 2 - (Real.log (m / U)) ^ 2) -
        ((Real.log t) ^ 2 - (Real.log (m / S)) ^ 2)| := by
          congr 1
          ring
    _ ≤ |(Real.log a) ^ 2 - (Real.log (m / U)) ^ 2| +
        |(Real.log t) ^ 2 - (Real.log (m / S)) ^ 2| := htri
    _ ≤ Ea * (2 * |Real.log (m / U)| + Ea) +
        Et * (2 * |Real.log (m / S)| + Et) := add_le_add ha2 ht2

/-- The scalar-box specialization with the exact endpoint error scales already
proved in `ScalarBoxLogScaleBounds` and `ScalarBoxPoleLogScaleBounds`. -/
theorem abs_log_square_pair_remainder_le_regulator
    {a t m S U δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (ha : |Real.log a - Real.log (m / U)| ≤ lowerLogError δ η)
    (ht : |Real.log t - Real.log (m / S)| ≤ poleLogError δ η) :
    |((Real.log a) ^ 2 - (Real.log t) ^ 2) -
      ((Real.log (m / U)) ^ 2 - (Real.log (m / S)) ^ 2)| ≤
      lowerLogError δ η *
          (2 * |Real.log (m / U)| + lowerLogError δ η) +
      poleLogError δ η *
          (2 * |Real.log (m / S)| + poleLogError δ η) := by
  rcases logError_nonneg hδ hη with ⟨hEa, hEt⟩
  exact abs_log_square_pair_remainder_le hEa hEt ha ht

end GppScalarBoxLogSquareRemainder

#print axioms GppScalarBoxLogSquareRemainder.logError_nonneg
#print axioms GppScalarBoxLogSquareRemainder.abs_sq_sub_sq_le_of_abs_sub_le
#print axioms GppScalarBoxLogSquareRemainder.abs_log_square_pair_remainder_le
#print axioms GppScalarBoxLogSquareRemainder.abs_log_square_pair_remainder_le_regulator
