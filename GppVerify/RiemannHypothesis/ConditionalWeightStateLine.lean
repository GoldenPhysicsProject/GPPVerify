import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import GppVerify.RiemannHypothesis.FunctionalEquation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Conditional theorem: weight states of a unitary dilation action sit on `Re s = 1/2`

Two premises are kept separate and named.

* **Physical unitarity (proved here, no hypothesis beyond the data).** If a
  unitary (norm-preserving) dilation action `U a` on a complex inner product
  space has a nonzero state `ψ` with `U a ψ = χ_s(a) ψ`, where `χ_s` is the
  half-density-normalized dilation character, then `Re s = 1/2`.
* **Arithmetic-physics correspondence (a hypothesis, `ArithmeticPhysicsCorrespondence`).**
  Every zero of the completed Riemann xi function is the weight of such a
  normalizable state. This is NOT proved and NOT asserted as an axiom. For
  any fixed `U` it implies that all xi zeros lie on `Re s = 1/2`, so it is at
  least as strong as RH. RH remains open.

The module therefore states exactly what RH would need from a physical
sector: a Hilbert space with unitary scale evolution whose normalizable
weights include every zero. It constructs no such space.
-/

namespace GppConditionalWeightState

open GppScaleMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `s` is the weight of a normalizable state of the dilation action `U`. -/
def IsWeightState (U : ℝ → H →ₗᵢ[ℂ] H) (s : ℂ) : Prop :=
  ∃ ψ : H, ψ ≠ 0 ∧ ∀ a : ℝ, 0 < a → U a ψ = dilationCharacter s a • ψ

/-- **Physical unitarity.** A weight of a normalizable state of a unitary
dilation action lies on the principal line `Re s = 1/2`. -/
theorem weight_state_re_half {U : ℝ → H →ₗᵢ[ℂ] H} {s : ℂ}
    (h : IsWeightState U s) : s.re = 1 / 2 := by
  obtain ⟨ψ, hψ, hU⟩ := h
  have h2 := hU 2 (by norm_num)
  have hn : ‖U 2 ψ‖ = ‖ψ‖ := (U 2).norm_map ψ
  rw [h2, norm_smul] at hn
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hunit : ‖dilationCharacter s 2‖ = 1 := by
    have : ‖dilationCharacter s 2‖ * ‖ψ‖ = 1 * ‖ψ‖ := by rw [one_mul]; exact hn
    exact mul_right_cancel₀ hpos.ne' this
  exact critical_line_of_dilation_unitary (by norm_num) (by norm_num) hunit

/-- The correspondence premise, named as a hypothesis: every zero of the
completed xi function is the weight of a normalizable state of `U`. -/
def ArithmeticPhysicsCorrespondence (U : ℝ → H →ₗᵢ[ℂ] H) : Prop :=
  ∀ ρ : ℂ, GppFE.riemannXi ρ = 0 → IsWeightState U ρ

/-- **Conditional theorem.** Physical unitarity plus the arithmetic-physics
correspondence put every xi zero on `Re s = 1/2`. -/
theorem xi_zeros_on_critical_line_of_correspondence
    {U : ℝ → H →ₗᵢ[ℂ] H} (hcorr : ArithmeticPhysicsCorrespondence U) :
    ∀ ρ : ℂ, GppFE.riemannXi ρ = 0 → ρ.re = 1 / 2 :=
  fun ρ hρ => weight_state_re_half (hcorr ρ hρ)

end GppConditionalWeightState

#print axioms GppConditionalWeightState.weight_state_re_half
#print axioms GppConditionalWeightState.xi_zeros_on_critical_line_of_correspondence
