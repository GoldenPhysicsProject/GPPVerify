import GppVerify.RiemannHypothesis.LogisticMobiusBoost
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The half-density Möbius action is unitary on the compact picture of the logistic line

Source: Codex, `research/codex/2026-10-03_logistic_compact_principal_series_bridge.md` §§2–4 (the part of the
note not covered by `LogisticMobiusBoost`).

In the compact coordinate `r = tanh(x/2) ∈ (−1, 1)` the logistic measure `p(x) dx` is `½ dr`
(`LogisticMobiusBoost`), and the boost `x ↦ x − t` acts as `φ_a(r) = (r − a)/(1 − a r)`, `a = tanh(t/2)`.
This file proves:

* `phi_mapsTo`, `phi_image`: for `|a| < 1`, `φ_a` is a bijection of `(−1, 1)` onto itself (inverse `φ_{−a}`);
* `change_of_variables`: `∫_{(−1,1)} φ_a'(r) g(φ_a(r)) dr = ∫_{(−1,1)} g(r) dr` for every `g`;
* `unitary_half_density`: with `(U_a F)(r) = √(φ_a'(r)) F(φ_a(r))`,
  `∫_{(−1,1)} (U_a F)² dr = ∫_{(−1,1)} F² dr` — the half-density Möbius action is isometric on
  `L²((−1, 1), dr/2)`, the compact picture of the one-dimensional principal series;
* `matrix_coefficient`: for `a = tanh(t/2)`, `t ≠ 0`, `½ ∫_{(−1,1)} √(φ_a'(r)) dr = t/(2 sinh(t/2))`, the matrix
  coefficient `⟨1, U_t 1⟩` of the unitary orbit (`= πv/sinh πv` at `t = 2πv`, the critical zero Gram kernel);
* `ratio_density`: `∫_0^∞ e^{−(1+e^u) y} e^u y dy = e^u/(1+e^u)² = p(u)`, the logistic density as the law of
  `log(X/Y)` for independent unit exponentials `X, Y`.

## Scope

Calculus on the interval and a Gamma integral. Surjectivity (a bijection of the interval) gives isometry, hence
unitarity of each `U_a` on real `L²`; the one-parameter group law in `t`, the generator
`G_ps = −∂_x + ½ tanh(x/2)` and the identification with the principal series of `SL(2,ℝ)` are not formalized.
Nothing here concerns the zeros of `ζ`. No RH claim.
-/

open MeasureTheory Set Real

namespace GppLogisticPS

/-- The Möbius boost `φ_a(r) = (r − a)/(1 − a r)`. -/
noncomputable def phi (a r : ℝ) : ℝ := (r - a) / (1 - a * r)

/-- Its derivative `φ_a'(r) = (1 − a²)/(1 − a r)²`. -/
noncomputable def dphi (a r : ℝ) : ℝ := (1 - a ^ 2) / (1 - a * r) ^ 2

lemma one_sub_mul_pos {a r : ℝ} (ha : |a| < 1) (hr : r ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - a * r := by
  obtain ⟨h1, h2⟩ := hr
  have hab : |a * r| < 1 := by
    rw [abs_mul]
    have : |r| < 1 := abs_lt.mpr ⟨h1, h2⟩
    calc |a| * |r| ≤ |a| * 1 := by gcongr
      _ < 1 := by simpa using ha
  have := (abs_lt.mp hab).2
  linarith

theorem phi_mapsTo {a : ℝ} (ha : |a| < 1) : MapsTo (phi a) (Ioo (-1) 1) (Ioo (-1) 1) := by
  intro r hr
  have hd := one_sub_mul_pos ha hr
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  unfold phi
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

theorem phi_phi_neg {a : ℝ} (ha : |a| < 1) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    phi a (phi (-a) y) = y := by
  have hd := one_sub_mul_pos (a := -a) (by simpa using ha) hy
  have hd' : 1 + a * y ≠ 0 := by
    have : 1 - -a * y = 1 + a * y := by ring
    rw [this] at hd; exact hd.ne'
  have ha2 : 1 - a ^ 2 ≠ 0 := by
    have := abs_lt.mp ha
    nlinarith
  unfold phi
  have e1 : (y - -a) / (1 - -a * y) = (y + a) / (1 + a * y) := by ring_nf
  rw [e1]
  have hd2 : 1 + y * a ≠ 0 := by rw [mul_comm]; exact hd'
  have hden : 1 - a * ((y + a) / (1 + a * y)) ≠ 0 := by
    have : 1 - a * ((y + a) / (1 + a * y)) = (1 - a ^ 2) / (1 + a * y) := by
      field_simp; ring
    rw [this]; exact div_ne_zero ha2 hd'
  rw [div_eq_iff hden]
  field_simp
  ring

theorem phi_image {a : ℝ} (ha : |a| < 1) : phi a '' Ioo (-1) 1 = Ioo (-1) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨r, hr, rfl⟩; exact phi_mapsTo ha hr
  · intro y hy
    have ha' : |-a| < 1 := by simpa using ha
    exact ⟨phi (-a) y, phi_mapsTo ha' hy, phi_phi_neg ha hy⟩

theorem phi_injOn {a : ℝ} (ha : |a| < 1) : InjOn (phi a) (Ioo (-1) 1) := by
  intro r hr s hs h
  have ha' : |-a| < 1 := by simpa using ha
  have hd := one_sub_mul_pos ha hr
  have hd' := one_sub_mul_pos ha hs
  unfold phi at h
  rw [div_eq_div_iff hd.ne' hd'.ne'] at h
  have ha2 : 1 - a ^ 2 ≠ 0 := by nlinarith [abs_lt.mp ha]
  have h3 : (r - s) * (1 - a ^ 2) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha2)

theorem hasDerivAt_phi {a r : ℝ} (ha : |a| < 1) (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (phi a) (dphi a r) r :=
  GppLogisticBoost.hasDerivAt_mobius a r (one_sub_mul_pos ha hr).ne'

theorem dphi_pos {a r : ℝ} (ha : |a| < 1) (hr : r ∈ Ioo (-1 : ℝ) 1) : 0 < dphi a r := by
  have hd := one_sub_mul_pos ha hr
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith [abs_lt.mp ha]
  unfold dphi; positivity

/-- **Change of variables for the Möbius boost** on the interval. -/
theorem change_of_variables {a : ℝ} (ha : |a| < 1) (g : ℝ → ℝ) :
    ∫ r in Ioo (-1 : ℝ) 1, dphi a r * g (phi a r) = ∫ r in Ioo (-1 : ℝ) 1, g r := by
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1))
    (f := phi a) (f' := dphi a)
    (fun r hr => (hasDerivAt_phi ha hr).hasDerivWithinAt) (phi_injOn ha) g
  rw [phi_image ha] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (dphi_pos ha hr)]

/-- **Unitarity of the half-density Möbius action:** `‖U_a F‖² = ‖F‖²` in `L²((−1,1), dr)`. -/
theorem unitary_half_density {a : ℝ} (ha : |a| < 1) (F : ℝ → ℝ) :
    ∫ r in Ioo (-1 : ℝ) 1, (Real.sqrt (dphi a r) * F (phi a r)) ^ 2 =
      ∫ r in Ioo (-1 : ℝ) 1, F r ^ 2 := by
  rw [← change_of_variables ha (fun r => F r ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  rw [mul_pow, Real.sq_sqrt (dphi_pos ha hr).le]

/-- **The logistic density as a ratio law:** `∫_0^∞ e^{−(1+e^u) y} e^u y dy = e^u/(1+e^u)²`. -/
theorem ratio_density (u : ℝ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-((1 + Real.exp u) * y)) * Real.exp u * y =
      Real.exp u / (1 + Real.exp u) ^ 2 := by
  have hc : 0 < 1 + Real.exp u := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 + Real.exp u) (by norm_num) hc
  have e : ∀ y : ℝ, Real.exp (-((1 + Real.exp u) * y)) * Real.exp u * y =
      Real.exp u * (y ^ (2 - 1 : ℝ) * Real.exp (-((1 + Real.exp u) * y))) := by
    intro y; norm_num [Real.rpow_one]; ring
  simp_rw [e]
  rw [integral_const_mul, h]
  have hg : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  rw [hg]
  norm_num [Real.rpow_two]
  field_simp

/-- The ratio law agrees with the logistic density `p`. -/
theorem ratio_density_eq_p (u : ℝ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-((1 + Real.exp u) * y)) * Real.exp u * y = GppLogisticBoost.p u := by
  rw [ratio_density, GppLogisticBoost.logistic_density_eq]

/-! ### The matrix coefficient `⟨1, U_t 1⟩ = t/(2 sinh(t/2))` -/

lemma one_sub_mul_pos_closed {a r : ℝ} (ha : |a| < 1) (hr : r ∈ Icc (-1 : ℝ) 1) : 0 < 1 - a * r := by
  have hr' : |r| ≤ 1 := abs_le.mpr hr
  have hab : |a * r| ≤ |a| := by
    rw [abs_mul]; calc |a| * |r| ≤ |a| * 1 := by gcongr
      _ = |a| := mul_one _
  have := (abs_le.mp hab).2
  have := (abs_lt.mp ha).2
  have h3 : a * r ≤ |a| := (abs_le.mp hab).2
  linarith [le_abs_self a, abs_nonneg a]

lemma tanh_half_lt_one (t : ℝ) : |Real.tanh (t / 2)| < 1 := by
  rw [abs_lt]
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

lemma one_add_div_one_sub_tanh (x : ℝ) :
    (1 + Real.tanh x) / (1 - Real.tanh x) = Real.exp (2 * x) := by
  have hc := (Real.cosh_pos x).ne'
  have h1 : 1 + Real.tanh x = Real.exp x / Real.cosh x := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp; rw [← Real.cosh_add_sinh]
  have h2 : 1 - Real.tanh x = Real.exp (-x) / Real.cosh x := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp; rw [← Real.cosh_sub_sinh]
  rw [h1, h2, div_div_div_cancel_right₀ hc, ← Real.exp_sub]; congr 1; ring

theorem matrix_coefficient {t : ℝ} (ht : t ≠ 0) :
    (1 / 2 : ℝ) * ∫ r in Ioo (-1 : ℝ) 1, Real.sqrt (dphi (Real.tanh (t / 2)) r) =
      t / (2 * Real.sinh (t / 2)) := by
  set a := Real.tanh (t / 2) with ha
  have hab : |a| < 1 := tanh_half_lt_one t
  have hc : 0 < Real.cosh (t / 2) := Real.cosh_pos _
  have hsh : Real.sinh (t / 2) ≠ 0 := by
    intro h
    apply ht
    have := Real.sinh_eq_zero.mp h
    linarith
  have ha0 : a ≠ 0 := by
    rw [ha, Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero hsh hc.ne'
  have h1a : 0 < 1 - a ^ 2 := by nlinarith [abs_lt.mp hab]
  have hsq : Real.sqrt (1 - a ^ 2) = 1 / Real.cosh (t / 2) := by
    rw [ha, Real.tanh_eq_sinh_div_cosh]
    have : 1 - (Real.sinh (t / 2) / Real.cosh (t / 2)) ^ 2 = (1 / Real.cosh (t / 2)) ^ 2 := by
      field_simp; nlinarith [Real.cosh_sq (t / 2)]
    rw [this, Real.sqrt_sq (by positivity)]
  -- pointwise: √(φ') = √(1−a²)/(1−a r)
  have hpt : ∀ r ∈ Ioo (-1 : ℝ) 1, Real.sqrt (dphi a r) = Real.sqrt (1 - a ^ 2) * (1 - a * r)⁻¹ := by
    intro r hr
    have hd := one_sub_mul_pos hab hr
    unfold dphi
    rw [Real.sqrt_div h1a.le, Real.sqrt_sq hd.le, div_eq_mul_inv]
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  -- ∫_{(−1,1)} (1 − a r)⁻¹ = (1/a) log((1+a)/(1−a))
  have hF : ∀ r ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt (fun r => -Real.log (1 - a * r) / a) ((1 - a * r)⁻¹) r := by
    intro r hr
    have hr' : r ∈ Icc (-1 : ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num)] at hr
    have hpos : 0 < 1 - a * r := one_sub_mul_pos_closed hab hr'
    have h2 : HasDerivAt (fun r : ℝ => 1 - a * r) (-a) r := by
      simpa using ((hasDerivAt_id r).const_mul a).const_sub 1
    have h3 := (h2.log hpos.ne').neg.div_const a
    refine h3.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun r : ℝ => (1 - a * r)⁻¹) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    intro r hr
    have hr' : r ∈ Icc (-1 : ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num)] at hr
    have hpos : 0 < 1 - a * r := one_sub_mul_pos_closed hab hr'
    exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).inv₀ hpos.ne' |>.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), hFTC]
  have hlog : -Real.log (1 - a * 1) / a - (-Real.log (1 - a * -1) / a) = t / a := by
    have h1 : 0 < 1 - a := by have := (abs_lt.mp hab).2; linarith
    have h2 : 0 < 1 + a := by have := (abs_lt.mp hab).1; linarith
    have : Real.log (1 + a) - Real.log (1 - a) = t := by
      rw [← Real.log_div h2.ne' h1.ne', ha, one_add_div_one_sub_tanh]
      rw [Real.log_exp]; ring
    simp only [mul_one, mul_neg]
    rw [sub_neg_eq_add, show 1 + a = 1 - -a by ring] at *
    field_simp
    linarith
  rw [hlog, hsq]
  have : a = Real.sinh (t / 2) / Real.cosh (t / 2) := by rw [ha, Real.tanh_eq_sinh_div_cosh]
  rw [this]
  field_simp

end GppLogisticPS
