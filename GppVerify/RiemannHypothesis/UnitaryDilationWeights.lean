import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The conformal weight of an eigenstate of a unitary dilation lies on `Re Δ = 1/2`

**Definition of the weight.** A state `ψ ≠ 0` of a Hilbert space on which a dilation acts by a
linear isometry `V` (the dilation by `a`) has *conformal weight* `Δ` when
`V ψ = a^{Δ - 1/2} ψ`: this is the action of `D_a f(x) = √a f(a x)` on `x^{Δ-1}`
(`ConformalShadow.dil_cpow`).

**Theorem (`re_weight_eq_half`).** If `a > 0`, `a ≠ 1`, and `V : H →ₗᵢ[ℂ] H` is a linear isometry
with `V ψ = a^{Δ - 1/2} ψ` for some `ψ ≠ 0`, then `Re Δ = 1/2`.  An eigenvalue of an isometry has
modulus one; this is the principal-series condition.

**The identification of `s` with `Δ`** is the statement that a zero `ρ` of `ζ` is the weight of such
an eigenstate (`IsWeight ρ`), and the reduction

  `riemannHypothesis_of_isWeight : (∀ nontrivial zero ρ, IsWeight ρ) → RiemannHypothesis`

shows exactly where the content sits: the hypothesis `IsWeight ρ` is equivalent to `Re ρ = 1/2`
(`isWeight_iff`), so supplying it for every zero is the Riemann Hypothesis.  What is needed is the
canonical Hilbert space, built from the primes, in which each zero is such an eigenstate.
-/

open Complex

namespace GppUnitaryWeights

/-- Eigenvalues of a linear isometry have modulus one. -/
theorem norm_eq_one_of_isometry_eigen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : H →ₗᵢ[ℂ] H) {ψ : H} (hψ : ψ ≠ 0) {c : ℂ} (h : V ψ = c • ψ) : ‖c‖ = 1 := by
  have h1 : ‖V ψ‖ = ‖ψ‖ := V.norm_map ψ
  rw [h, norm_smul] at h1
  have hn : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  have : ‖c‖ * ‖ψ‖ = 1 * ‖ψ‖ := by rw [one_mul]; exact h1
  exact mul_right_cancel₀ hn.ne' this

/-- **The weight of a unitary dilation eigenstate lies on `Re Δ = 1/2`.** -/
theorem re_weight_eq_half {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : H →ₗᵢ[ℂ] H) {ψ : H} (hψ : ψ ≠ 0) {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) {Δ : ℂ}
    (h : V ψ = ((a : ℝ) : ℂ) ^ (Δ - 1 / 2) • ψ) : Δ.re = 1 / 2 := by
  have hn := norm_eq_one_of_isometry_eigen V hψ h
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha] at hn
  have hre : (Δ - 1 / 2).re = Δ.re - 1 / 2 := by simp
  rw [hre] at hn
  have hlog : (Δ.re - 1 / 2) * Real.log a = 0 := by
    have := congrArg Real.log hn
    rwa [Real.log_rpow ha, Real.log_one] at this
  have hlog_ne : Real.log a ≠ 0 := by
    intro h0
    rcases Real.log_eq_zero.1 h0 with h | h | h <;> [exact ha.ne' h; exact ha1 h; linarith]
  have := (mul_eq_zero.1 hlog).resolve_right hlog_ne
  linarith

/-- `ρ` is the conformal weight of a nonzero eigenstate of a linear isometry acting as a dilation
by `2`. -/
def IsWeight (ρ : ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (V : H →ₗᵢ[ℂ] H) (ψ : H),
    ψ ≠ 0 ∧ V ψ = (((2 : ℝ) : ℂ)) ^ (ρ - 1 / 2) • ψ

theorem isWeight_re {ρ : ℂ} (h : IsWeight ρ) : ρ.re = 1 / 2 := by
  obtain ⟨H, _, _, V, ψ, hψ, hV⟩ := h
  exact re_weight_eq_half V hψ (by norm_num) (by norm_num) hV

/-- Every `ρ` with `Re ρ = 1/2` is such a weight (one-dimensional model). -/
theorem isWeight_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : IsWeight ρ := by
  have hn : ‖(((2 : ℝ) : ℂ)) ^ (ρ - 1 / 2)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : (ρ - 1 / 2).re = 0 := by simp [h]
    rw [this, Real.rpow_zero]
  let V : ℂ →ₗᵢ[ℂ] ℂ :=
    { toLinearMap := LinearMap.lsmul ℂ ℂ (((2 : ℝ) : ℂ) ^ (ρ - 1 / 2))
      norm_map' := fun x => by
        simp only [LinearMap.lsmul_apply, smul_eq_mul, norm_mul, hn, one_mul] }
  exact ⟨ℂ, inferInstance, inferInstance, V, 1, one_ne_zero, rfl⟩

theorem isWeight_iff (ρ : ℂ) : IsWeight ρ ↔ ρ.re = 1 / 2 := ⟨isWeight_re, isWeight_of_re⟩

/-- **The reduction.** If every nontrivial zero of `ζ` is the conformal weight of a nonzero
eigenstate of a unitary dilation, then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_isWeight
    (h : ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → IsWeight ρ) :
    RiemannHypothesis := fun ρ hz ht h1 => isWeight_re (h ρ hz ht h1)

end GppUnitaryWeights

#print axioms GppUnitaryWeights.re_weight_eq_half
#print axioms GppUnitaryWeights.isWeight_iff
#print axioms GppUnitaryWeights.riemannHypothesis_of_isWeight
