import GppVerify.RiemannHypothesis.LogisticMobiusBoost
import GppVerify.RiemannHypothesis.ThreeLineLogistic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Off-line displacement is the mean orientation bias of the tilted logistic state

Source: Codex, `research/codex/2026-10-03_logistic_compact_principal_series_bridge.md` §5.

For `z = δ + iγ` the zero vector is normalised by the probability density
`dμ_δ(x) = p(x) e^{2δx} dx / M(2δ)`, with `p(x) = 1/(4cosh²(x/2))` the logistic density. Since
`p'/p = −tanh(x/2)`, integrating the total derivative of `p e^{2δx}` over the line gives
`E_{μ_δ}[tanh(x/2)] = 2δ`. This file proves, for `|δ| < 1/2` (the range in which `M(2δ) < ∞`):

* `hasDerivAt_p`: `p'(x) = −tanh(x/2) p(x)`;
* `integrable_tilt`: `p(x) e^{2δx}` is integrable on `ℝ`;
* `tilt_integral_tanh`: `∫ tanh(x/2) p(x) e^{2δx} dx = 2δ ∫ p(x) e^{2δx} dx`, i.e.
  `Re ρ − 1/2 = ½ E_{μ_z}[r]` with `r = tanh(x/2)` and `δ = Re ρ − 1/2`;
* `mean_tanh_eq`: the same as an expectation (`M > 0`).

On the critical line `δ = 0` the expectation vanishes (`tilt_integral_tanh` at `δ = 0`: the ratio law is
balanced).

## Scope

An exact identity about the one-parameter tilted logistic family. It says the *exponent* `2δ` of the tilt is
measured by the orientation observable `tanh(x/2)`; it does not say that the arithmetic zero states are
balanced (that is RH), and it does not involve `ζ`. No RH claim.
-/

open MeasureTheory Set Real

namespace GppOrientationBias

/-- The logistic density (from `LogisticMobiusBoost`). -/
noncomputable abbrev p : ℝ → ℝ := GppLogisticBoost.p

/-- The tilted density `p(x) e^{2δx}`. -/
noncomputable def tilt (δ x : ℝ) : ℝ := p x * Real.exp (2 * δ * x)

theorem hasDerivAt_p (x : ℝ) : HasDerivAt p (-(Real.tanh (x / 2)) * p x) x := by
  have hc : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have h2 := (Real.hasDerivAt_cosh (x / 2)).comp x h1
  have h3 : HasDerivAt (fun y : ℝ => 4 * Real.cosh (y / 2) ^ 2)
      (4 * (2 * Real.cosh (x / 2) * (Real.sinh (x / 2) * (1 / 2)))) x := by
    have := (h2.pow 2).const_mul 4
    simpa [Function.comp_def] using this
  have h4 := (hasDerivAt_const x (1 : ℝ)).div h3 (by positivity)
  have e : p = fun y => 1 / (4 * Real.cosh (y / 2) ^ 2) := rfl
  rw [e]
  refine h4.congr_deriv ?_
  beta_reduce
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

theorem p_le_exp_neg_abs (x : ℝ) : p x ≤ Real.exp (-|x|) := by
  unfold p GppLogisticBoost.p
  have hw : 4 * Real.cosh (x / 2) ^ 2 = Real.exp x + 2 + Real.exp (-x) := GppThreeLineLogistic.wInv_eq x
  rw [hw]
  have h1 : Real.exp |x| ≤ Real.exp x + 2 + Real.exp (-x) := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
    · rw [abs_of_nonpos h]; linarith [Real.exp_pos x]
  rw [show Real.exp (-|x|) = (Real.exp |x|)⁻¹ from Real.exp_neg _, one_div]
  exact inv_anti₀ (Real.exp_pos _) h1

lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  set g : ℝ → ℝ := (Ici (0 : ℝ)).indicator (fun x => Real.exp (-c * x)) with hg
  have hgi : Integrable g :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (exp_neg_integrableOn_Ioi 0 hc)).integrable_indicator
      measurableSet_Ici
  have hsum : Integrable (fun x => g x + g (-x)) := hgi.add hgi.comp_neg
  refine hsum.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Measurable fun x : ℝ => Real.exp (-c * |x|)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
      have h1 : g x = Real.exp (-c * x) := by rw [hg]; simp [Set.indicator_of_mem (mem_Ici.mpr h)]
      have h2 : 0 ≤ g (-x) := by rw [hg]; exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
      linarith
    · rw [abs_of_nonpos h]
      have h1 : g (-x) = Real.exp (-c * (-x)) := by
        rw [hg]; simp [Set.indicator_of_mem (mem_Ici.mpr (neg_nonneg.mpr h))]
      have h2 : 0 ≤ g x := by rw [hg]; exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
      linarith

theorem continuous_p : Continuous p := continuous_iff_continuousAt.2 fun x => (hasDerivAt_p x).continuousAt

theorem tilt_nonneg (δ x : ℝ) : 0 ≤ tilt δ x := by
  unfold tilt
  exact mul_nonneg (GppLogisticBoost.p_pos x).le (Real.exp_pos _).le

theorem continuous_tilt (δ : ℝ) : Continuous (tilt δ) := by
  unfold tilt
  exact continuous_p.mul (by fun_prop)

/-- `M(2δ) = ∫ p e^{2δx}` is finite for `|δ| < 1/2`. -/
theorem integrable_tilt {δ : ℝ} (hδ : |δ| < 1 / 2) : Integrable (tilt δ) := by
  have hc : 0 < 1 - 2 * |δ| := by linarith
  refine (integrable_exp_neg_mul_abs hc).mono' (continuous_tilt δ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tilt_nonneg δ x)]
  unfold tilt
  have h1 := p_le_exp_neg_abs x
  have h2 : Real.exp (2 * δ * x) ≤ Real.exp (2 * |δ| * |x|) := by
    apply Real.exp_le_exp.mpr
    have : δ * x ≤ |δ| * |x| := by rw [← abs_mul]; exact le_abs_self _
    linarith
  calc p x * Real.exp (2 * δ * x) ≤ Real.exp (-|x|) * Real.exp (2 * |δ| * |x|) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(1 - 2 * |δ|) * |x|) := by rw [← Real.exp_add]; congr 1; ring

theorem continuous_tanh_half : Continuous fun x : ℝ => Real.tanh (x / 2) := by
  have : (fun x : ℝ => Real.tanh (x / 2)) = fun x => Real.sinh (x / 2) / Real.cosh (x / 2) := by
    funext x; exact Real.tanh_eq_sinh_div_cosh _
  rw [this]
  exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) (fun x => (Real.cosh_pos _).ne')

theorem hasDerivAt_tilt (δ x : ℝ) :
    HasDerivAt (tilt δ) ((-(Real.tanh (x / 2)) + 2 * δ) * tilt δ x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (2 * δ * y)) (Real.exp (2 * δ * x) * (2 * δ)) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * δ)).exp
  have := (hasDerivAt_p x).mul h1
  unfold tilt
  refine this.congr_deriv ?_
  ring

/-- **The orientation observable measures the tilt.** For `|δ| < 1/2`,
`∫ tanh(x/2) p(x) e^{2δx} dx = 2δ ∫ p(x) e^{2δx} dx`. -/
theorem tilt_integral_tanh {δ : ℝ} (hδ : |δ| < 1 / 2) :
    ∫ x, Real.tanh (x / 2) * tilt δ x = 2 * δ * ∫ x, tilt δ x := by
  have hint := integrable_tilt hδ
  have hbd : ∀ x, |(-(Real.tanh (x / 2)) + 2 * δ)| ≤ 1 + 2 * |δ| := by
    intro x
    have h1 : |Real.tanh (x / 2)| ≤ 1 := (abs_lt.mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le
    calc |(-(Real.tanh (x / 2)) + 2 * δ)| ≤ |-(Real.tanh (x / 2))| + |2 * δ| := abs_add_le _ _
      _ ≤ 1 + 2 * |δ| := by rw [abs_neg, abs_mul]; norm_num; linarith
  have hderiv_int : Integrable (fun x => (-(Real.tanh (x / 2)) + 2 * δ) * tilt δ x) := by
    refine (hint.const_mul (1 + 2 * |δ|)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((continuous_tanh_half.neg).add continuous_const).mul
        (continuous_tilt δ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tilt_nonneg δ x)]
      exact mul_le_mul_of_nonneg_right (hbd x) (tilt_nonneg δ x)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_tilt δ) hderiv_int hint
  have hth : Integrable (fun x => Real.tanh (x / 2) * tilt δ x) := by
    refine hint.mono' (continuous_tanh_half.mul (continuous_tilt δ)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tilt_nonneg δ x)]
    have h1 : |Real.tanh (x / 2)| ≤ 1 := (abs_lt.mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le
    calc |Real.tanh (x / 2)| * tilt δ x ≤ 1 * tilt δ x :=
          mul_le_mul_of_nonneg_right h1 (tilt_nonneg δ x)
      _ = tilt δ x := one_mul _
  have e : (fun x => (-(Real.tanh (x / 2)) + 2 * δ) * tilt δ x) =
      fun x => -(Real.tanh (x / 2) * tilt δ x) + 2 * δ * tilt δ x := by
    funext x; ring
  rw [e] at h0
  have h1 : ∫ x, (-(Real.tanh (x / 2) * tilt δ x) + 2 * δ * tilt δ x) =
      (-∫ x, Real.tanh (x / 2) * tilt δ x) + 2 * δ * ∫ x, tilt δ x := by
    have := integral_add (μ := volume) (f := fun x => -(Real.tanh (x / 2) * tilt δ x))
      (g := fun x => 2 * δ * tilt δ x) hth.neg (hint.const_mul (2 * δ))
    rw [this, integral_neg, integral_const_mul]
  linarith

/-- **`E_{μ_δ}[tanh(x/2)] = 2δ`** for the normalised tilted logistic law. -/
theorem mean_tanh_eq {δ : ℝ} (hδ : |δ| < 1 / 2) :
    (∫ x, Real.tanh (x / 2) * tilt δ x) / ∫ x, tilt δ x = 2 * δ := by
  have hM : 0 < ∫ x, tilt δ x := by
    rw [integral_pos_iff_support_of_nonneg (tilt_nonneg δ) (integrable_tilt hδ)]
    have : Function.support (tilt δ) = univ := by
      ext x; simp only [Function.mem_support, mem_univ, iff_true]
      unfold tilt
      exact (mul_pos (GppLogisticBoost.p_pos x) (Real.exp_pos _)).ne'
    rw [this]; simp
  rw [tilt_integral_tanh hδ]
  field_simp

end GppOrientationBias
