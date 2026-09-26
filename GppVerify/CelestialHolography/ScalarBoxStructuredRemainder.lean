import GppVerify.CelestialHolography.ScalarBoxLogSquareRemainder
import Mathlib.Tactic

/-!
# Structured scalar-box remainder assembly

This file formalizes the algebraic core of the final regulated scalar-box remainder.
It keeps the endpoint logarithmic errors and the small special-function remainder
separate, matching the discovery-side structured bound.
-/

namespace GppScalarBoxStructuredRemainder

/-- Exact algebraic identity behind the structured scalar-box remainder. -/
theorem core_remainder_identity
    (ellU ellS da dt E : ℝ) :
    ((ellU + da) * (ellS + dt) + (1 / 2 : ℝ) * (ellU + da) ^ 2 + E) -
        (ellU * ellS + (1 / 2 : ℝ) * ellU ^ 2) =
      da * (ellS + ellU) + ellU * dt + da * dt +
        (1 / 2 : ℝ) * da ^ 2 + E := by
  ring

/-- If `|da|≤A`, `|dt|≤B`, and `|E|≤Estar`, then the exact core remainder
is bounded by the structured five-term majorant used in the scalar-box limit. -/
theorem abs_core_remainder_le
    {ellU ellS da dt E A B Estar : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hE0 : 0 ≤ Estar)
    (hda : |da| ≤ A) (hdt : |dt| ≤ B) (hE : |E| ≤ Estar) :
    |da * (ellS + ellU) + ellU * dt + da * dt +
        (1 / 2 : ℝ) * da ^ 2 + E| ≤
      A * (|ellS| + |ellU|) + |ellU| * B + A * B +
        (1 / 2 : ℝ) * A ^ 2 + Estar := by
  have hsum : |ellS + ellU| ≤ |ellS| + |ellU| := abs_add _ _
  have h1 : |da * (ellS + ellU)| ≤ A * (|ellS| + |ellU|) := by
    rw [abs_mul]
    calc
      |da| * |ellS + ellU| ≤ A * |ellS + ellU| :=
        mul_le_mul_of_nonneg_right hda (abs_nonneg _)
      _ ≤ A * (|ellS| + |ellU|) :=
        mul_le_mul_of_nonneg_left hsum hA0
  have h2 : |ellU * dt| ≤ |ellU| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdt (abs_nonneg _)
  have h3 : |da * dt| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul hda hdt (abs_nonneg _) hA0
  have hsq : |da| ^ 2 ≤ A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hA0] using hda
  have h4 : |(1 / 2 : ℝ) * da ^ 2| ≤ (1 / 2 : ℝ) * A ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_pow]
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  calc
    |da * (ellS + ellU) + ellU * dt + da * dt +
        (1 / 2 : ℝ) * da ^ 2 + E| ≤
      |da * (ellS + ellU)| + |ellU * dt| + |da * dt| +
        |(1 / 2 : ℝ) * da ^ 2| + |E| := by
          calc
            |da * (ellS + ellU) + ellU * dt + da * dt +
                (1 / 2 : ℝ) * da ^ 2 + E| ≤
              |da * (ellS + ellU) + ellU * dt + da * dt +
                (1 / 2 : ℝ) * da ^ 2| + |E| := abs_add _ _
            _ ≤ (|da * (ellS + ellU) + ellU * dt + da * dt| +
                  |(1 / 2 : ℝ) * da ^ 2|) + |E| := by
                  gcongr
                  exact abs_add _ _
            _ ≤ ((|da * (ellS + ellU) + ellU * dt| + |da * dt|) +
                  |(1 / 2 : ℝ) * da ^ 2|) + |E| := by
                  gcongr
                  exact abs_add _ _
            _ ≤ (((|da * (ellS + ellU)| + |ellU * dt|) + |da * dt|) +
                  |(1 / 2 : ℝ) * da ^ 2|) + |E| := by
                  gcongr
                  exact abs_add _ _
            _ = |da * (ellS + ellU)| + |ellU * dt| + |da * dt| +
                  |(1 / 2 : ℝ) * da ^ 2| + |E| := by ring
    _ ≤ A * (|ellS| + |ellU|) + |ellU| * B + A * B +
          (1 / 2 : ℝ) * A ^ 2 + Estar := by
      linarith

/-- Direct bound for the difference between the moving-log core and its massless
scale model. The common constant term (e.g. `-π²/6`) cancels automatically. -/
theorem abs_structured_core_difference_le
    {ellU ellS da dt E A B Estar c : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hE0 : 0 ≤ Estar)
    (hda : |da| ≤ A) (hdt : |dt| ≤ B) (hE : |E| ≤ Estar) :
    |((ellU + da) * (ellS + dt) + (1 / 2 : ℝ) * (ellU + da) ^ 2 + c + E) -
      (ellU * ellS + (1 / 2 : ℝ) * ellU ^ 2 + c)| ≤
      A * (|ellS| + |ellU|) + |ellU| * B + A * B +
        (1 / 2 : ℝ) * A ^ 2 + Estar := by
  rw [show ((ellU + da) * (ellS + dt) + (1 / 2 : ℝ) * (ellU + da) ^ 2 + c + E) -
      (ellU * ellS + (1 / 2 : ℝ) * ellU ^ 2 + c) =
      da * (ellS + ellU) + ellU * dt + da * dt +
        (1 / 2 : ℝ) * da ^ 2 + E by ring]
  exact abs_core_remainder_le hA0 hB0 hE0 hda hdt hE

end GppScalarBoxStructuredRemainder

#print axioms GppScalarBoxStructuredRemainder.core_remainder_identity
#print axioms GppScalarBoxStructuredRemainder.abs_core_remainder_le
#print axioms GppScalarBoxStructuredRemainder.abs_structured_core_difference_le
