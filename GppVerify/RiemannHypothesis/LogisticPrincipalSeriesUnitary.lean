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

end GppLogisticPS
