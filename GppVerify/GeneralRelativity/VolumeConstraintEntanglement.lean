import Mathlib.Tactic
import GppVerify.QuantumGravity.CausalDiamondFisherCancellation
import GppVerify.QuantumGravity.CausalDiamondGammaBridge

/-!
# Volume constraint and entanglement equilibrium: formalized exact core

Daniel Toupin, Golden Physics Project, 2026-10-16.

All propositions below specify their hypotheses. In particular the
Einstein/CKV conformal Ricci identity is a geometric input and NOT
silently deduced from an undeclared metric connection. The full
covariant symplectic current, KL spectral transform and type-III
entropy first law are not formalized here.
-/

namespace GppVolumeConstraint

open scoped BigOperators

section StateResponse
variable {n : ℕ}

/-- State response at a fixed reference modular generator. -/
def stateResponse (dp K : Fin n → ℝ) : ℝ := ∑ i, dp i * K i

/-- Normalized-state tangent vectors annihilate a scalar identity shift. -/
theorem normalized_state_scalar_invisible (dp K : Fin n → ℝ) (c : ℝ)
    (hzero : ∑ i, dp i = 0) :
    stateResponse dp (fun i => K i + c) = stateResponse dp K := by
  unfold stateResponse
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hc : (∑ i : Fin n, dp i * c) = (∑ i : Fin n, dp i) * c := by
    rw [Finset.sum_mul]
  rw [hc, hzero]
  simp

/-- In contrast, changing the scalar part of an operator contributes to
its full expectation derivative even in a normalized reference state. -/
theorem normalized_operator_scalar_visible (p dK : Fin n → ℝ) (c : ℝ)
    (hone : ∑ i, p i = 1) :
    (∑ i, p i * (dK i + c)) = (∑ i, p i * dK i) + c := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hc : (∑ i : Fin n, p i * c) = (∑ i : Fin n, p i) * c := by
    rw [Finset.sum_mul]
  rw [hc, hone]
  ring
end StateResponse

section VacuumShift
/-- The cosmological equation is invariant under simultaneous constant
vacuum-energy and cosmological-term shifts. -/
theorem vacuum_shift (einstein lambda metric stress q : ℝ) :
    einstein + lambda * metric = stress ↔
    einstein + (lambda - q) * metric = stress - q * metric := by
  constructor <;> intro h <;> nlinarith [h]

/-- Entropy-volume multiplier is nonzero for a positive entropy density and
finite flat round ball, even though the background cosmological term can be 0. -/
theorem volume_multiplier_nonzero (eta ell : ℝ)
    (heta : eta ≠ 0) (hell : ell ≠ 0) :
    -(eta * (2 / ell)) ≠ 0 := by
  apply neg_ne_zero.mpr
  exact mul_ne_zero heta (div_ne_zero (by norm_num) hell)
end VacuumShift

section ConformalGeometry
/-- Algebraic extraction of the conformal-factor wave equation from
the traced Einstein/CKV Ricci-variation identity. -/
theorem ricci_trace_wave (d R alpha lap : ℝ)
    (hd1 : d - 1 ≠ 0)
    (htrace : (d - 2) * lap + d * lap = -(2 * R) * alpha) :
    lap = -(R / (d - 1)) * alpha := by
  have h2 : (d - 1) * lap = -(R * alpha) := by nlinarith [htrace]
  have h2' : (d - 1) * (-(R / (d - 1)) * alpha) = -(R * alpha) := by
    field_simp [hd1]
  have : (d - 1) * lap =
      (d - 1) * (-(R / (d - 1)) * alpha) := by rw [h2, h2']
  exact mul_left_cancel₀ hd1 this

/-- Einstein-background concircularity, in components, given precisely the
two differential-geometric inputs that a full connection-level proof needs. -/
theorem einstein_ricci_identity_concircular
    {n : ℕ} (d R alpha lap : ℝ)
    (g hess : Fin n → Fin n → ℝ)
    (hd : d ≠ 0) (hd1 : d - 1 ≠ 0) (hd2 : d - 2 ≠ 0)
    (hwave : lap = -(R / (d - 1)) * alpha)
    (hRicci : ∀ i j,
       (d - 2) * hess i j + g i j * lap =
         -(2 * R / d) * alpha * g i j) :
    ∀ i j, hess i j = -(R / (d * (d - 1))) * alpha * g i j := by
  intro i j
  have h := hRicci i j
  rw [hwave] at h
  have hmul : (d - 2) * hess i j =
      (d - 2) * (-(R / (d * (d - 1))) * alpha * g i j) := by
    calc
      (d - 2) * hess i j =
          -(2 * R / d) * alpha * g i j -
            g i j * (-(R / (d - 1)) * alpha) := by linarith [h]
      _ = (d - 2) * (-(R / (d * (d - 1))) * alpha * g i j) := by
        field_simp [hd, hd1]
        ring
  exact mul_left_cancel₀ hd2 hmul
end ConformalGeometry

section Ensemble
/-- Jacobson fixed-volume RNC deficit, with the common geometric factor
Q = Ω_(d-2) ell^d Rhat factored out. -/
theorem fixed_volume_area_deficit
    (d Q : ℝ) (hd1 : d - 1 ≠ 0) (hdplus : d + 1 ≠ 0) :
    -Q / (6 * (d - 1)) -
      (d - 2) * (-Q / (6 * (d - 1) * (d + 1))) =
        -Q / (2 * (d^2 - 1)) := by
  have hprod : d^2 - 1 ≠ 0 := by
    have hh : (d - 1) * (d + 1) ≠ 0 := mul_ne_zero hd1 hdplus
    convert hh using 1 <;> ring
  field_simp [hd1, hdplus, hprod]
  ring

/-- Area admixture residual exactly equals a/2 at first curvature order,
for the family of constraints F=A^a V^b. -/
theorem area_admixture_residual (d a b : ℝ)
    (hd1 : d - 1 ≠ 0) (hdplus : d + 1 ≠ 0) :
    (d - 1) * (d + 1) *
       (a / (6 * (d - 1)) + b / (6 * (d + 1))) -
       (a * (d - 2) + b * (d - 1)) / 6 = a / 2 := by
  field_simp [hd1, hdplus]
  ring

/-- The fixed-radius ensemble has a different Newton normalization in 4D. -/
theorem radius_factor_4d : (3 : ℝ) / (4 + 1) = 3 / 5 := by norm_num

/-- The frozen-conformal-weight diagnostic coefficient in 4D; this
does NOT assert invariant geometric variation of a curved CKV. -/
theorem frozen_weight_factor_4d :
    (3 * (4 : ℝ) * (4 + 3)) / (2 * (4 + 1) * (3 * 4 - 1)) = 42 / 55 := by
  norm_num
end Ensemble

section Spectral
/-- Exact KL thermal cancellation: imported established GPPVerify theorem. -/
theorem thermal_fisher_cancellation (lam : ℝ)
    (hsinh : Real.sinh (Real.pi * lam) ≠ 0) :
    GppCausalDiamondFisher.klDensity lam *
      GppCausalDiamondFisher.bwFisherKernel lam =
        (2 / Real.pi) * lam ^ 2 := by
  exact GppCausalDiamondFisher.klDensity_mul_bwFisherKernel lam hsinh

/-- Cubic suppression is a conditional model factorization; regularity
of arbitrary trace-class spectral responses is NOT proved. -/
theorem cubic_model (lam c rho : ℝ)
    (hrho : rho = (2 / Real.pi) * lam ^ 2) :
    rho * lam * c = (2 / Real.pi) * lam ^ 3 * c := by
  rw [hrho]
  ring
end Spectral


section HyperplaneUniqueness

/-- On an admissible real variation space, a nonzero work coefficient and
stationarity along ker F force the volume differential to be proportional
to F. This is first-order hyperplane uniqueness, not global F=f(V). -/
theorem stationarity_selects_volume_tangent
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F V : E →ₗ[ℝ] ℝ) (w : E) (hw : F w = 1)
    (C : ℝ) (hC : C ≠ 0)
    (hstat : ∀ x, F x = 0 → C * V x = 0) :
    V = (V w) • F := by
  apply LinearMap.ext
  intro x
  have hFx : F (x - (F x) • w) = 0 := by
    simp [map_sub, map_smul, hw]
  have hwork := hstat (x - (F x) • w) hFx
  have hzero : V (x - (F x) • w) = 0 :=
    (mul_eq_zero.mp hwork).resolve_left hC
  have hv : V x - F x * V w = 0 := by
    simpa [map_sub, map_smul] using hzero
  change V x = (V w) * F x
  nlinarith [hv]

end HyperplaneUniqueness

end GppVolumeConstraint

#print axioms GppVolumeConstraint.normalized_state_scalar_invisible
#print axioms GppVolumeConstraint.einstein_ricci_identity_concircular
#print axioms GppVolumeConstraint.area_admixture_residual
#print axioms GppVolumeConstraint.thermal_fisher_cancellation

#print axioms GppVolumeConstraint.stationarity_selects_volume_tangent
