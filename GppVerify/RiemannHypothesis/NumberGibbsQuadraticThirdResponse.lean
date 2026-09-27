import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuHessian
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticHigherMomentDerivatives
import Mathlib.Tactic

/-!
# Third Massieu response of the quadratically confined number gas

The Hessian of the Massieu potential is the covariance matrix of the sufficient
statistics `(L,L^2)`.  Differentiating its entries with the certified raw-moment
derivative ladder gives the symmetric third responses.  They are the negative
normalized joint third cumulants.
-/

namespace GppNumberGibbsQuadraticThirdResponse

open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticPartitionDerivatives
open GppNumberGibbsQuadraticMomentDerivatives
open GppNumberGibbsQuadraticHigherMomentDerivatives
open GppNumberGibbsQuadraticMassieuHessian

/-- Normalized third cumulant `κ(L,L,L)`. -/
noncomputable def kappa111 (β η : ℝ) : ℝ :=
  (M3 β η * Z β η ^ 2 - 3 * M1 β η * M2 β η * Z β η + 2 * M1 β η ^ 3) /
    Z β η ^ 3

/-- Normalized joint third cumulant `κ(L,L,L²)`. -/
noncomputable def kappa112 (β η : ℝ) : ℝ :=
  (M4 β η * Z β η ^ 2 - M2 β η ^ 2 * Z β η -
      2 * M1 β η * M3 β η * Z β η + 2 * M1 β η ^ 2 * M2 β η) /
    Z β η ^ 3

/-- Normalized joint third cumulant `κ(L,L²,L²)`. -/
noncomputable def kappa122 (β η : ℝ) : ℝ :=
  (M5 β η * Z β η ^ 2 - 2 * M2 β η * M3 β η * Z β η -
      M1 β η * M4 β η * Z β η + 2 * M1 β η * M2 β η ^ 2) /
    Z β η ^ 3

/-- Normalized third cumulant `κ(L²,L²,L²)`. -/
noncomputable def kappa222 (β η : ℝ) : ℝ :=
  (M6 β η * Z β η ^ 2 - 3 * M2 β η * M4 β η * Z β η + 2 * M2 β η ^ 3) /
    Z β η ^ 3

/-- `∂β g_{ββ} = -κ(L,L,L)`, equivalently the `βββ` Massieu response. -/
theorem hasDerivAt_fisherBB_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => fisherBB b η) (-kappa111 β η) β := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hnum :=
    ((hasDerivAt_M2_beta β hη).mul (hasDerivAt_Z_beta β hη)).sub
      ((hasDerivAt_M1_beta β hη).mul (hasDerivAt_M1_beta β hη))
  have hden := (hasDerivAt_Z_beta β hη).pow 2
  have H := hnum.div hden (pow_ne_zero 2 hZne)
  convert H using 1 <;> simp [fisherBB, kappa111] <;> field_simp [hZne] <;> ring

/-- `∂η g_{ββ} = -κ(L,L,L²)`, equivalently the `ββη` Massieu response. -/
theorem hasDerivAt_fisherBB_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => fisherBB β e) (-kappa112 β η) η := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hnum :=
    ((hasDerivAt_M2_eta β hη).mul (hasDerivAt_Z_eta β hη)).sub
      ((hasDerivAt_M1_eta β hη).mul (hasDerivAt_M1_eta β hη))
  have hden := (hasDerivAt_Z_eta β hη).pow 2
  have H := hnum.div hden (pow_ne_zero 2 hZne)
  convert H using 1 <;> simp [fisherBB, kappa112] <;> field_simp [hZne] <;> ring

/-- `∂β g_{βη} = -κ(L,L,L²)`.  This makes the `ββη` permutation symmetry
explicit at the Fisher-matrix level. -/
theorem hasDerivAt_fisherBE_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => fisherBE b η) (-kappa112 β η) β := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hnum :=
    ((hasDerivAt_M3_beta β hη).mul (hasDerivAt_Z_beta β hη)).sub
      ((hasDerivAt_M1_beta β hη).mul (hasDerivAt_M2_beta β hη))
  have hden := (hasDerivAt_Z_beta β hη).pow 2
  have H := hnum.div hden (pow_ne_zero 2 hZne)
  convert H using 1 <;> simp [fisherBE, kappa112] <;> field_simp [hZne] <;> ring

/-- `∂η g_{βη} = -κ(L,L²,L²)`.  This makes the `βηη` permutation symmetry
explicit at the Fisher-matrix level. -/
theorem hasDerivAt_fisherBE_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => fisherBE β e) (-kappa122 β η) η := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hnum :=
    ((hasDerivAt_M3_eta β hη).mul (hasDerivAt_Z_eta β hη)).sub
      ((hasDerivAt_M1_eta β hη).mul (hasDerivAt_M2_eta β hη))
  have hden := (hasDerivAt_Z_eta β hη).pow 2
  have H := hnum.div hden (pow_ne_zero 2 hZne)
  convert H using 1 <;> simp [fisherBE, kappa122] <;> field_simp [hZne] <;> ring

/-- `∂β g_{ηη} = -κ(L,L²,L²)`, equivalently the `βηη` Massieu response. -/
theorem hasDerivAt_fisherEE_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => fisherEE b η) (-kappa122 β η) β := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hnum :=
    ((hasDerivAt_M4_beta β hη).mul (hasDerivAt_Z_beta β hη)).sub
      ((hasDerivAt_M2_beta β hη).mul (hasDerivAt_M2_beta β hη))
  have hden := (hasDerivAt_Z_beta β hη).pow 2
  have H := hnum.div hden (pow_ne_zero 2 hZne)
  convert H using 1 <;> simp [fisherEE, kappa122] <;> field_simp [hZne] <;> ring

/-- `∂η g_{ηη} = -κ(L²,L²,L²)`, equivalently the `ηηη` Massieu response. -/
theorem hasDerivAt_fisherEE_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => fisherEE β e) (-kappa222 β η) η := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hnum :=
    ((hasDerivAt_M4_eta β hη).mul (hasDerivAt_Z_eta β hη)).sub
      ((hasDerivAt_M2_eta β hη).mul (hasDerivAt_M2_eta β hη))
  have hden := (hasDerivAt_Z_eta β hη).pow 2
  have H := hnum.div hden (pow_ne_zero 2 hZne)
  convert H using 1 <;> simp [fisherEE, kappa222] <;> field_simp [hZne] <;> ring

#print axioms hasDerivAt_fisherBB_beta
#print axioms hasDerivAt_fisherBB_eta
#print axioms hasDerivAt_fisherBE_beta
#print axioms hasDerivAt_fisherBE_eta
#print axioms hasDerivAt_fisherEE_beta
#print axioms hasDerivAt_fisherEE_eta

end GppNumberGibbsQuadraticThirdResponse
