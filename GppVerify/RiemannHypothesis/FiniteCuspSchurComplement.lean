import Mathlib.Tactic

/-!
# Retaining the scalar Schur-complement coupling and determinant factor

This is the two-channel algebraic core of the co-Poisson boundary audit.
It does not construct the infinite arithmetic boundary operator.
-/

namespace GppFiniteCuspSchurComplement

def fullDet (a c b z : ℝ) : ℝ :=
  (a - z) * (c - z) - b ^ 2

noncomputable def schur (a c b z : ℝ) : ℝ :=
  a - z - b ^ 2 / (c - z)

/-- Exact elimination retains both the coupling and the eliminated factor. -/
theorem fullDet_eq_eliminated_factor_mul_schur
    (a c b z : ℝ) (hc : c - z ≠ 0) :
    fullDet a c b z = (c - z) * schur a c b z := by
  unfold fullDet schur
  field_simp [hc]
  <;> ring

/-- Dropping a nonzero coupling changes the determinant. -/
theorem nonzero_coupling_changes_determinant
    (a c b z : ℝ) (hb : b ≠ 0) :
    fullDet a c b z ≠ (a - z) * (c - z) := by
  unfold fullDet
  have hsq : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  intro h
  linarith

/-- Away from the eliminated level, exact elimination preserves zeros. -/
theorem fullDet_zero_iff_schur_zero
    (a c b z : ℝ) (hc : c - z ≠ 0) :
    fullDet a c b z = 0 ↔ schur a c b z = 0 := by
  rw [fullDet_eq_eliminated_factor_mul_schur a c b z hc]
  exact mul_eq_zero.trans (or_iff_right (fun h => hc h))

end GppFiniteCuspSchurComplement
