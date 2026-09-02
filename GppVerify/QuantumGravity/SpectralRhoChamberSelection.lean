import GppVerify.QuantumGravity.SpectralRhoRecurrence
import Mathlib.Tactic

/-!
# Exact adjacent-chamber selection window

The normalized Gamma-family step ratio crossing is completely explicit.  For
`k > 0`, the step entering chamber `k` is larger than one while the step leaving
it is smaller than one exactly on

  k < 2 x^2 < k+1.

This is a local selection statement for the recurrence factors only.  It does
not assume or assert that the Gamma chambers arise from repeated convolution.
-/

namespace GppSpectralRhoChamberSelection

open GppSpectralRho

/-- Exact two-sided window in which the adjacent recurrence factors select
chamber `k`: the incoming factor exceeds one and the outgoing factor is below
one iff `2*x^2` lies strictly between `k` and `k+1`. -/
theorem adjacent_step_selection_iff
    {k : ℕ} (hk : 0 < k) (x : ℝ) :
    1 < rhoStepFactor (k - 1) x ∧ rhoStepFactor k x < 1 ↔
      (k : ℝ) < 2 * x ^ 2 ∧ 2 * x ^ 2 < (k : ℝ) + 1 := by
  have hkm1 : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
    omega
  rw [rhoStepFactor_gt_one_iff, rhoStepFactor_lt_one_iff, hkm1]

/-- The selected chamber index, if it exists, is unique: two natural numbers
cannot both contain the same real number `2*x^2` in their open unit interval. -/
theorem selection_index_unique
    {k l : ℕ} {x : ℝ}
    (hk : (k : ℝ) < 2 * x ^ 2) (hk' : 2 * x ^ 2 < (k : ℝ) + 1)
    (hl : (l : ℝ) < 2 * x ^ 2) (hl' : 2 * x ^ 2 < (l : ℝ) + 1) :
    k = l := by
  by_contra hne
  have hkl : k < l ∨ l < k := Nat.lt_or_gt_of_ne hne
  cases hkl with
  | inl hkl =>
      have hcast : (k : ℝ) + 1 ≤ (l : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hkl
      linarith
  | inr hlk =>
      have hcast : (l : ℝ) + 1 ≤ (k : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hlk
      linarith

end GppSpectralRhoChamberSelection

#print axioms GppSpectralRhoChamberSelection.adjacent_step_selection_iff
#print axioms GppSpectralRhoChamberSelection.selection_index_unique
