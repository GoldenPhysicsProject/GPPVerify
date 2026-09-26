import Mathlib.Tactic

/-!
# Critical n-gon residue / radial-shell algebra

This file records the exact scalar algebra linking the critical n-gon residue
magnitude `1/((n-1)(n-2))` to the normalized second transverse-mass moment
`(n-2)/(n-1)`. The analytic derivation of the residue and radial measure is
kept in separate modules/Discovery records.
-/

namespace GppCriticalNgonRadialAlgebra

/-- Universal magnitude of the critical scalar n-gon residue, written for a
real parameter so the normalization algebra is transparent. -/
def criticalResidueMagnitude (n : ℝ) : ℝ :=
  1 / ((n - 1) * (n - 2))

/-- Normalized critical-shell second moment `E[(2μ/M)^2]`. -/
def normalizedMuSqMoment (n : ℝ) : ℝ :=
  (n - 2) / (n - 1)

/-- The residue magnitude times the normalized second transverse-mass moment
collapses to the exact square law `1/(n-1)^2`. -/
theorem residue_mul_muSqMoment_eq_square
    {n : ℝ} (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    criticalResidueMagnitude n * normalizedMuSqMoment n =
      1 / (n - 1) ^ 2 := by
  unfold criticalResidueMagnitude normalizedMuSqMoment
  field_simp [hn1, hn2]
  ring

/-- Triangle member of the hierarchy. -/
theorem n_three_value :
    criticalResidueMagnitude 3 = (1 / 2 : ℝ) ∧
    normalizedMuSqMoment 3 = (1 / 2 : ℝ) := by
  norm_num [criticalResidueMagnitude, normalizedMuSqMoment]

/-- Box member of the hierarchy. -/
theorem n_four_value :
    criticalResidueMagnitude 4 = (1 / 6 : ℝ) ∧
    normalizedMuSqMoment 4 = (2 / 3 : ℝ) := by
  norm_num [criticalResidueMagnitude, normalizedMuSqMoment]

end GppCriticalNgonRadialAlgebra

#print axioms GppCriticalNgonRadialAlgebra.residue_mul_muSqMoment_eq_square
#print axioms GppCriticalNgonRadialAlgebra.n_three_value
#print axioms GppCriticalNgonRadialAlgebra.n_four_value
