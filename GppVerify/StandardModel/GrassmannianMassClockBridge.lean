import Mathlib.Tactic
import GppVerify.GrassmannianComplexDifferential
import GppVerify.StandardModel.GrassmannianPhysicalMass
import GppVerify.StandardModel.OrientationMassTime

/-!
# Grassmannian inverse scale, physical mass, and the Compton ruler/clock

For a Grassmannian big-cell matrix assembled from the two massive spinor roots,
the chart determinant has modulus `m`.  The complex Grassmannian differential
has eigenvalues `ζ/D`, with `|ζ|=1`.  Therefore every such eigendirection has
inverse-mass modulus `1/m`.  Restoring `ℏ,c` converts that dimensionless inverse
mass into the reduced Compton length.
-/

namespace GppGrassmannianMassClockBridge

open GppMassOrientationCoupling
open GppOrientationMassTime

/-- The complex big-cell determinant evaluated on the physical spinor-pair
columns is exactly the `physicalSpinorChartDet`. -/
theorem complexD_physical_eq (p00 p11 : ℝ) (p01 : ℂ) :
    GppGrassmannianComplexDifferential.D
      (lambda1 p00 p01).1 (lambda2 p00 p11 p01).1
      (lambda1 p00 p01).2 (lambda2 p00 p11 p01).2
      = physicalSpinorChartDet p00 p11 p01 := by
  simp [GppGrassmannianComplexDifferential.D,
    physicalSpinorChartDet, complexChartDet]

/-- On the positive mass shell the physically assembled Grassmannian
coordinate determinant has modulus exactly `m`. -/
theorem complexD_physical_norm_eq_mass
    {p00 p11 m : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    ‖GppGrassmannianComplexDifferential.D
      (lambda1 p00 p01).1 (lambda2 p00 p11 p01).1
      (lambda1 p00 p01).2 (lambda2 p00 p11 p01).2‖ = m := by
  rw [complexD_physical_eq]
  exact physicalSpinorChartDet_norm_eq_mass hp00 hdet hm hmass

/-- Unit-phase divided by the physical chart determinant has exact inverse-mass
modulus. -/
theorem physical_inverse_mass_eigenvalue_scale
    {D ζ : ℂ} {m : ℝ} (hm : 0 < m) (hD : ‖D‖ = m) (hζ : ‖ζ‖ = 1) :
    ‖ζ / D‖ = 1 / m := by
  rw [norm_div, hζ, hD]

/-- Restoring units turns the Grassmannian inverse-mass scale into the reduced
Compton wavelength: `lambda_C = (hbar/c) * |ζ/D|`. -/
theorem comptonLength_eq_quantum_scale_mul_inverseMass
    {D ζ : ℂ} {m c hbar : ℝ}
    (hm : 0 < m) (hc : c ≠ 0) (hD : ‖D‖ = m) (hζ : ‖ζ‖ = 1) :
    comptonLength m c hbar = (hbar / c) * ‖ζ / D‖ := by
  rw [physical_inverse_mass_eigenvalue_scale hm hD hζ]
  simp [comptonLength]
  field_simp [hm.ne', hc]
  ring

/-- The reciprocal statement for the Compton clock: multiplying its frequency
by the Grassmannian inverse-mass spectral scale gives `c^2/hbar`. -/
theorem comptonFrequency_mul_inverseMass
    {D ζ : ℂ} {m c hbar : ℝ}
    (hm : 0 < m) (hh : hbar ≠ 0) (hD : ‖D‖ = m) (hζ : ‖ζ‖ = 1) :
    comptonFrequency m c hbar * ‖ζ / D‖ = c ^ 2 / hbar := by
  rw [physical_inverse_mass_eigenvalue_scale hm hD hζ]
  simp [comptonFrequency]
  field_simp [hm.ne', hh]
  ring

end GppGrassmannianMassClockBridge
