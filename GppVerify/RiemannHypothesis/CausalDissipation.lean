import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Causal dissipation identity for regulator removal

Source: Astra, GPP-bridge `work/2026-10-21_astra_balanced_inverse_energy.md` (which itself proposes
this Lean promotion). Formalized by Claude Code, with AI assistance, for Daniel Toupin / Golden
Physics Project.

The inverse of Codex's balanced regulator acts as two causal first-order stages. For one stage with
state `q`, `q(0) = 0`, input `v = q' + (a+e) q` and output `w = q' + a q`:

* `stage_sq_diff`: `v² − w² = e · 2 q q' + e(2a+e) q²` (pointwise);
* `stage_energy_identity`: `∫₀ᵀ (v² − w²) = e q(T)² + e(2a+e) ∫₀ᵀ q²`, exactly, on every finite
  interval;
* `stage_contraction`: for `a, e ≥ 0` the stage does not increase `∫₀ᵀ (·)²`;
* `log_energy_transfer`: if `E₀ ≤ e^{2eT} E_e` then `log(1+E₀) ≤ 2eT + log(1+E_e)`, the step behind
  Astra's diagonal-schedule criterion.

Applying the stage with `a = 0` and then `a = ½` gives Astra's `E₀(T) ≤ e^{2eT} E_e(T)`; that
composition (solving the two ODEs for the prime signal) and the Laplace/pole argument are not
formalized here. Real-valued signals only. The identity removes no arithmetic difficulty: it bounds
`E₀` by `E_e`, and no upper bound on `E_e` is known. Nothing here concerns RH beyond that.
-/

open intervalIntegral

namespace GppCausalDissipation

/-- Pointwise algebra of one causal stage. -/
theorem stage_sq_diff (q q' a e : ℝ) :
    (q' + (a + e) * q) ^ 2 - (q' + a * q) ^ 2 = e * (2 * q * q') + e * (2 * a + e) * q ^ 2 := by
  ring

/-- **Causal dissipation identity** (one stage). If `q(0) = 0`, `v = q' + (a+e) q` and
`w = q' + a q`, then `∫₀ᵀ (v² − w²) = e q(T)² + e(2a+e) ∫₀ᵀ q²`. -/
theorem stage_energy_identity {q q' : ℝ → ℝ} (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq' : Continuous q') (h0 : q 0 = 0) (a e T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((q' t + (a + e) * q t) ^ 2 - (q' t + a * q t) ^ 2)) =
      e * q T ^ 2 + e * (2 * a + e) * ∫ t in (0 : ℝ)..T, q t ^ 2 := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun t => (hq t).continuousAt
  have hsq : ∀ t, HasDerivAt (fun s => q s ^ 2) (2 * q t * q' t) t := by
    intro t
    have h := (hq t).mul (hq t)
    have e1 : (fun s => q s ^ 2) = fun s => q s * q s := funext fun s => sq (q s)
    rw [e1]
    exact h.congr_deriv (by ring)
  have hint1 : IntervalIntegrable (fun t => 2 * q t * q' t) MeasureTheory.volume 0 T :=
    ((continuous_const.mul hqc).mul hq').intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => q t ^ 2) MeasureTheory.volume 0 T :=
    (hqc.pow 2).intervalIntegrable _ _
  have hftc : (∫ t in (0 : ℝ)..T, 2 * q t * q' t) = q T ^ 2 - q 0 ^ 2 :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hsq t) hint1
  simp_rw [stage_sq_diff]
  rw [integral_add (hint1.const_mul e) (hint2.const_mul _), integral_const_mul,
    integral_const_mul, hftc, h0]
  ring

/-- Each stage is an energy contraction for `a, e ≥ 0`. -/
theorem stage_contraction {q q' : ℝ → ℝ} (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq' : Continuous q') (h0 : q 0 = 0) {a e T : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (q' t + a * q t) ^ 2) ≤ ∫ t in (0 : ℝ)..T, (q' t + (a + e) * q t) ^ 2 := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun t => (hq t).continuousAt
  have hid := stage_energy_identity hq hq' h0 a e T
  have hi1 : IntervalIntegrable (fun t => (q' t + (a + e) * q t) ^ 2) MeasureTheory.volume 0 T :=
    ((hq'.add (continuous_const.mul hqc)).pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t => (q' t + a * q t) ^ 2) MeasureTheory.volume 0 T :=
    ((hq'.add (continuous_const.mul hqc)).pow 2).intervalIntegrable _ _
  rw [integral_sub hi1 hi2] at hid
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..T, q t ^ 2 :=
    integral_nonneg hT fun t _ => sq_nonneg _
  have : 0 ≤ e * q T ^ 2 + e * (2 * a + e) * ∫ t in (0 : ℝ)..T, q t ^ 2 := by positivity
  linarith

/-- Diagonal schedule step: `E₀ ≤ e^{2eT} E_e` gives `log(1+E₀) ≤ 2eT + log(1+E_e)`. -/
theorem log_energy_transfer {E0 Ee e T : ℝ} (hE0 : 0 ≤ E0) (hEe : 0 ≤ Ee) (he : 0 ≤ e) (hT : 0 ≤ T)
    (h : E0 ≤ Real.exp (2 * e * T) * Ee) :
    Real.log (1 + E0) ≤ 2 * e * T + Real.log (1 + Ee) := by
  have hexp : 1 ≤ Real.exp (2 * e * T) := Real.one_le_exp (by positivity)
  have h1 : 1 + E0 ≤ Real.exp (2 * e * T) * (1 + Ee) := by nlinarith
  have := Real.log_le_log (by linarith) h1
  rwa [Real.log_mul (by positivity) (by linarith), Real.log_exp] at this

end GppCausalDissipation
