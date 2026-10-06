import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Prime-family incidence: the 3--5--7 path and the 2--3 boundary lift

This file formalizes only the finite algebra behind the exploratory arithmetic-family
construction recorded in GPP-bridge on 2026-10-06.

For positive edge weights `a,b`, the weighted graph Laplacian of the path
`3--5--7` is positive semidefinite and has a protected constant zero mode.  Its
characteristic determinant factors as

  λ (λ² - 2(a+b) λ + 3ab).

Adjoining the exceptional gap-one edge `2--3` with weight `c`, pinning the
`p=2` boundary node, and taking the principal Dirichlet minor gives determinant
`abc`.  Thus positive `a,b,c` remove the null direction.

A more general 2×2 edge covariance with off-diagonal entry `x` still has the
constant zero mode; its characteristic determinant is

  λ (λ² - 2(a+b-x) λ + 3(ab-x²)).

No particle identification, neutrino phenomenology, Standard-Model derivation, or
dark-matter claim is formalized here.
-/

namespace GppPrimeFamilyIncidence

/-- Weighted graph Laplacian of the three-vertex path 3--5--7. -/
def neutralLaplacian (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, -a, 0;
     -a, a + b, -b;
     0, -b, b]

/-- Principal Dirichlet minor obtained from the four-vertex path 2--3--5--7
after pinning the p=2 boundary node. -/
def chargedDirichletLaplacian (c a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c + a, -a, 0;
     -a, a + b, -b;
     0, -b, b]

/-- The neutral three-path always has zero determinant. -/
theorem neutral_det_zero (a b : ℝ) :
    (neutralLaplacian a b).det = 0 := by
  rw [neutralLaplacian, Matrix.det_fin_three]
  simp
  ring

/-- The boundary-pinned three-by-three Dirichlet minor has determinant abc. -/
theorem charged_dirichlet_det (c a b : ℝ) :
    (chargedDirichletLaplacian c a b).det = a * b * c := by
  rw [chargedDirichletLaplacian, Matrix.det_fin_three]
  simp
  ring

/-- Positive boundary and edge weights make the Dirichlet determinant positive. -/
theorem charged_dirichlet_det_pos {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    0 < (chargedDirichletLaplacian c a b).det := by
  rw [charged_dirichlet_det]
  positivity

/-- Scalar quadratic energy of the neutral path. -/
def neutralEnergy (a b x₁ x₂ x₃ : ℝ) : ℝ :=
  a * (x₁ - x₂) ^ 2 + b * (x₂ - x₃) ^ 2

/-- The neutral collision energy is nonnegative for nonnegative conductances. -/
theorem neutral_energy_nonneg {a b x₁ x₂ x₃ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ neutralEnergy a b x₁ x₂ x₃ := by
  unfold neutralEnergy
  positivity

/-- With positive conductances the only zero-energy configurations are constants. -/
theorem neutral_energy_eq_zero_iff {a b x₁ x₂ x₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    neutralEnergy a b x₁ x₂ x₃ = 0 ↔ x₁ = x₂ ∧ x₂ = x₃ := by
  constructor
  · intro h
    have h1n : 0 ≤ a * (x₁ - x₂) ^ 2 := by positivity
    have h2n : 0 ≤ b * (x₂ - x₃) ^ 2 := by positivity
    have h1 : a * (x₁ - x₂) ^ 2 = 0 := by
      unfold neutralEnergy at h
      linarith
    have h2 : b * (x₂ - x₃) ^ 2 = 0 := by
      unfold neutralEnergy at h
      linarith
    have hs1 : (x₁ - x₂) ^ 2 = 0 := by
      exact (mul_eq_zero.mp h1).resolve_left (ne_of_gt ha)
    have hs2 : (x₂ - x₃) ^ 2 = 0 := by
      exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt hb)
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [neutralEnergy]

/-- Characteristic matrix λI-L for the neutral path. -/
def neutralSpectralMatrix (λ a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![λ - a, a, 0;
     a, λ - a - b, b;
     0, b, λ - b]

/-- Exact characteristic determinant of the weighted neutral path. -/
theorem neutral_characteristic (λ a b : ℝ) :
    (neutralSpectralMatrix λ a b).det =
      λ * (λ ^ 2 - 2 * (a + b) * λ + 3 * a * b) := by
  rw [neutralSpectralMatrix, Matrix.det_fin_three]
  simp
  ring

/-- At equal edge weights g, the characteristic polynomial is
λ(λ-g)(λ-3g), i.e. eigenvalues 0,g,3g. -/
theorem equal_weight_characteristic (λ g : ℝ) :
    (neutralSpectralMatrix λ g g).det =
      λ * (λ - g) * (λ - 3 * g) := by
  rw [neutral_characteristic]
  ring

/-- Three-by-three family operator induced by a symmetric edge covariance
C = [[a,x],[x,b]] through the incidence map B C Bᵀ. -/
def covarianceMass (a b x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, -a + x, -x;
     -a + x, a + b - 2 * x, -b + x;
     -x, -b + x, b]

/-- The general edge-covariance family operator retains a zero determinant. -/
theorem covariance_det_zero (a b x : ℝ) :
    (covarianceMass a b x).det = 0 := by
  rw [covarianceMass, Matrix.det_fin_three]
  simp
  ring

/-- Characteristic matrix λI-M for the general edge covariance. -/
def covarianceSpectralMatrix (λ a b x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![λ - a, a - x, x;
     a - x, λ - a - b + 2 * x, b - x;
     x, b - x, λ - b]

/-- The two nonzero spectral invariants are controlled by
trace' = 2(a+b-x) and product' = 3(ab-x²). -/
theorem covariance_characteristic (λ a b x : ℝ) :
    (covarianceSpectralMatrix λ a b x).det =
      λ * (λ ^ 2 - 2 * (a + b - x) * λ + 3 * (a * b - x ^ 2)) := by
  rw [covarianceSpectralMatrix, Matrix.det_fin_three]
  simp
  ring

end GppPrimeFamilyIncidence

#print axioms GppPrimeFamilyIncidence.neutral_det_zero
#print axioms GppPrimeFamilyIncidence.charged_dirichlet_det
#print axioms GppPrimeFamilyIncidence.neutral_energy_eq_zero_iff
#print axioms GppPrimeFamilyIncidence.neutral_characteristic
#print axioms GppPrimeFamilyIncidence.covariance_characteristic
