import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import GppVerify.RiemannHypothesis.FunctionalEquation
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree
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
  Every zero of the entire completed xi function `GppLogDerivZeroFree.xi` is the
  weight of such a normalizable state. (Repair 2026-11-06, after Codex #488: the
  legacy product `GppFE.riemannXi` vanishes at 0 and 1 because Lean totalizes the
  completed zeta at its poles, which made the earlier form of this premise
  unsatisfiable; `legacy_correspondence_empty` records that.) This is NOT proved and NOT asserted as an axiom. For
  any fixed `U` it implies that all xi zeros lie on `Re s = 1/2`, so it is at
  least as strong as RH. RH remains open.

The module therefore states exactly what RH would need from a physical
sector: a Hilbert space with unitary scale evolution whose normalizable
weights include every zero. It constructs no such space.
-/

namespace GppConditionalWeightState

open GppScaleMass Complex

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
  ∀ ρ : ℂ, GppLogDerivZeroFree.xi ρ = 0 → IsWeightState U ρ

/-- **Conditional theorem.** Physical unitarity plus the arithmetic-physics
correspondence put every xi zero on `Re s = 1/2`. -/
theorem xi_zeros_on_critical_line_of_correspondence
    {U : ℝ → H →ₗᵢ[ℂ] H} (hcorr : ArithmeticPhysicsCorrespondence U) :
    ∀ ρ : ℂ, GppLogDerivZeroFree.xi ρ = 0 → ρ.re = 1 / 2 :=
  fun ρ hρ => weight_state_re_half (hcorr ρ hρ)

/-- Zeros of the entire xi on the line give Mathlib's `RiemannHypothesis`.
(Proof pattern from Codex #488.) -/
theorem riemannHypothesis_of_entire_xi_zeros_on_line
    (h : ∀ ρ : ℂ, GppLogDerivZeroFree.xi ρ = 0 → ρ.re = 1 / 2) : RiemannHypothesis := by
  intro s hz htriv h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hg : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hs0 (by simpa using hn)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      exact htriv ⟨m, by rw [hn]; push_cast; ring⟩
  exact h s (GppLogDerivZeroFree.xi_eq_zero_of_zeta_zero hz hs0 h1 hg)

/-- **Conditional RH.** The correspondence premise (not proved) gives Mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_correspondence
    {U : ℝ → H →ₗᵢ[ℂ] H} (hcorr : ArithmeticPhysicsCorrespondence U) :
    RiemannHypothesis :=
  riemannHypothesis_of_entire_xi_zeros_on_line
    (xi_zeros_on_critical_line_of_correspondence hcorr)

/-- Regression: the legacy form of the premise, with `GppFE.riemannXi`, is
unsatisfiable, because `GppFE.riemannXi 0 = 0` and `Re 0 ≠ 1/2`. -/
theorem legacy_correspondence_empty (U : ℝ → H →ₗᵢ[ℂ] H) :
    ¬ (∀ ρ : ℂ, GppFE.riemannXi ρ = 0 → IsWeightState U ρ) := by
  intro h
  have h0 : GppFE.riemannXi 0 = 0 := by simp [GppFE.riemannXi]
  have := weight_state_re_half (h 0 h0)
  norm_num at this

end GppConditionalWeightState

#print axioms GppConditionalWeightState.weight_state_re_half
#print axioms GppConditionalWeightState.xi_zeros_on_critical_line_of_correspondence
