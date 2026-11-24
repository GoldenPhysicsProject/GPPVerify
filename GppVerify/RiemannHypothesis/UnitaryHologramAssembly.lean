import GppVerify.RiemannHypothesis.NymanBeurlingBoundStates
import GppVerify.RiemannHypothesis.BoundStateRenormalization
import GppVerify.RiemannHypothesis.PasterskiShaoNormalizability

/-!
# The assembly: the Riemann Hypothesis is exactly the absence of bound states

This module connects the Nyman–Beurling bound-state picture (`NymanBeurlingBoundStates`), the
renormalization trichotomy (`BoundStateRenormalization`) and the Pasterski–Shao normalizability
line (`PasterskiShaoNormalizability`) into one statement.

* `isNormalizable_iff`: the zero-state `x^{ρ-1}` on `(0, 1]` is square-integrable iff `re ρ > 1/2`.
* `IsBoundState ρ`: a zero of `ζ` in the strip whose state is normalizable;
  `NoBoundStates` says there is none.
* `riemannHypothesis_iff_noBoundStates`: **`RiemannHypothesis ↔ NoBoundStates`**, both directions,
  against Mathlib's `RiemannHypothesis`.
* `zeroState_dictionary`: at any zero in the strip the state is orthogonal to every Beurling
  function and pairs with the constant `1` to `1/ρ`; it is normalizable iff `re ρ > 1/2`; its
  regulated norm is finite above the line, renormalizes to `1` on it and diverges below.

The equivalence is proved; the statement `NoBoundStates` is the open content.
-/

open Complex MeasureTheory Set Filter Topology

namespace GppUnitaryHologram

open GppNymanBeurling GppBoundStateRenormalization

/-- The zero-state `x^{ρ-1}` on `(0, 1]` is normalizable: its squared norm is integrable. -/
def IsNormalizable (ρ : ℂ) : Prop :=
  IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2) (Ioc 0 1)

/-- Normalizable exactly when `re ρ > 1/2`. -/
theorem isNormalizable_iff (ρ : ℂ) : IsNormalizable ρ ↔ 1 / 2 < ρ.re := by
  refine ⟨fun h => ?_, integrableOn_norm_cpow_sq⟩
  rw [IsNormalizable, integrableOn_Ioc_iff_integrableOn_Ioo] at h
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2 * ρ.re - 2)) (Ioo 0 1) := by
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
    show ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2 = x ^ (2 * ρ.re - 2)
    rw [norm_cpow_eq_rpow_re_of_pos hx.1, ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    simp; ring_nf
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).1 h2
  linarith

/-- A bound state: a zero in the critical strip whose state is normalizable. -/
def IsBoundState (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ IsNormalizable ρ

/-- **Absence of bound states.** -/
def NoBoundStates : Prop := ∀ ρ : ℂ, ¬ IsBoundState ρ

/-- **The Riemann Hypothesis is exactly the absence of bound states.** Both directions. -/
theorem riemannHypothesis_iff_noBoundStates : RiemannHypothesis ↔ NoBoundStates := by
  constructor
  · intro hRH ρ ⟨hz, h0, h1, hn⟩
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
    have htriv : ¬ ∃ n : ℕ, ρ = -2 * (n + 1) := by
      rintro ⟨n, hn'⟩
      have := congrArg Complex.re hn'
      simp at this
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := hRH ρ hz htriv hρ1
    have h3 := (isNormalizable_iff ρ).1 hn
    linarith
  · intro hN
    apply GppOneSidedRH.riemannHypothesis_of_ne_zero
    intro s hs
    rcases lt_or_ge s.re 1 with h1 | h1
    · intro hz
      exact hN s ⟨hz, by linarith, h1, (isNormalizable_iff s).2 hs⟩
    · exact riemannZeta_ne_zero_of_one_le_re h1

/-- **The bound-state dictionary at a zero in the strip.** The state `x^{ρ-1}` is orthogonal to every
Beurling function and pairs with the constant `1` to give `1/ρ`; it is normalizable iff `re ρ > 1/2`;
and the regulated norm is finite above the line, renormalizes to `1` on it, and diverges below. -/
theorem zeroState_dictionary {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    (∀ θ : ℝ, 0 < θ → θ ≤ 1 →
        ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling θ x = 0) ∧
      ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) = 1 / ρ ∧
      (IsNormalizable ρ ↔ 1 / 2 < ρ.re) ∧
      (1 / 2 < ρ.re → Tendsto (regNorm ρ.re) (𝓝[>] 0) (𝓝 (1 / (2 * ρ.re - 1)))) ∧
      (ρ.re = 1 / 2 → ∀ ε : ℝ, 0 < ε → ε < 1 → regNorm (1 / 2) ε / (-Real.log ε) = 1) ∧
      (ρ.re < 1 / 2 → Tendsto (regNorm ρ.re) (𝓝[>] 0) atTop) :=
  ⟨fun _ hθ hθ1 => beurling_orthogonal hθ hθ1 h0 h1 hz, integral_Ioc_cpow_sub_one h0,
    isNormalizable_iff ρ, regNorm_tendsto_of_gt,
    fun _ _ hε hε1 => renormalized_norm_half hε hε1,
    regNorm_tendsto_atTop_of_lt⟩

#print axioms isNormalizable_iff
#print axioms riemannHypothesis_iff_noBoundStates
#print axioms zeroState_dictionary

end GppUnitaryHologram
