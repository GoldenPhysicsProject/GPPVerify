import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The Stieltjes–Mellin dispersion kernel

Source: Codex's `codex.formalization_queue` row "Formalize universal Stieltjes-Mellin dispersion
kernel" (priority 82; the row text is the specification, the queue status is not trusted).

* `stieltjes_mellin`: for `0 < Re σ < 1`,
  `∫₀^∞ x^{σ−1}/(1 + x) dx = π / sin(πσ)`: the Mellin transform of the Stieltjes kernel
  `(1 + x)⁻¹` gives the factor `π/sin(πσ)`.
* `beta_one_sub`: the Beta-integral side, `B(σ, 1−σ) = π/sin(πσ)` (from `Γ(σ)Γ(1−σ)` and `Γ(1) = 1`).
* `dispersion_factor`: with the Cutkosky normalization factor `8π` fixed in the source, the
  combined factor is `8π · π/sin(πσ) = 8π²/sin(πσ)`, the note's
  `M_J(σ) = (8π²/sin(πσ)) · M_C(σ)`. Here `M_J` and `M_C` themselves are not defined in Verify; the
  statement is the scalar factor only.

The proof substitutes `x = t/(1−t)`, a diffeomorphism `(0,1) → (0,∞)` with derivative `1/(1−t)²`,
which turns the Mellin integral into the Beta integral
`∫₀¹ t^{σ−1}(1−t)^{−σ} dt`. The row asks that the analytic-strip and Fubini hypotheses stay
explicit: `0 < Re σ < 1` is exactly the strip, and no Fubini step is used here.

## Scope

A closed-form Mellin integral. It does not touch the scalar-box regulator DCT or the Yang–Mills
numerator sewing, as the row says. No RH claim.
-/

open Complex MeasureTheory Set

namespace GppStieltjesMellin

lemma image_div_one_sub : (fun t : ℝ => t / (1 - t)) '' Ioo 0 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact div_pos ht0 (by linarith)
  · intro hx
    have hx0 : 0 < x := hx
    refine ⟨x / (1 + x), ⟨div_pos hx0 (by linarith), ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · have h1 : (1 : ℝ) + x ≠ 0 := by linarith
      have h2 : 1 - x / (1 + x) = 1 / (1 + x) := by field_simp; ring
      show x / (1 + x) / (1 - x / (1 + x)) = x
      rw [h2]; field_simp

lemma injOn_div_one_sub : InjOn (fun t : ℝ => t / (1 - t)) (Ioo 0 1) := by
  intro a ha b hb h
  have h : a / (1 - a) = b / (1 - b) := h
  have ha' : (1 : ℝ) - a ≠ 0 := by linarith [ha.2]
  have hb' : (1 : ℝ) - b ≠ 0 := by linarith [hb.2]
  rw [div_eq_div_iff ha' hb'] at h
  nlinarith

lemma hasDerivWithinAt_div_one_sub (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivWithinAt (fun t : ℝ => t / (1 - t)) (1 / (1 - t) ^ 2) (Ioo 0 1) t := by
  have h1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
  have hd : HasDerivAt (fun t : ℝ => t / (1 - t)) (1 / (1 - t) ^ 2) t := by
    have hs : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) t :=
      HasDerivAt.fun_sub (hasDerivAt_const t (1 : ℝ)) (hasDerivAt_id t)
    have h := (hasDerivAt_id t).fun_div hs h1
    exact HasDerivAt.congr_deriv h (by simp)
  exact hd.hasDerivWithinAt

theorem beta_one_sub (σ : ℂ) (h0 : 0 < σ.re) (h1 : σ.re < 1) :
    Complex.betaIntegral σ (1 - σ) = Real.pi / Complex.sin (Real.pi * σ) := by
  have hv : 0 < (1 - σ).re := by simp; linarith
  have := Complex.betaIntegral_eq_Gamma_mul_div σ (1 - σ) h0 hv
  rw [this, show σ + (1 - σ) = 1 by ring, Complex.Gamma_one, div_one]
  exact Complex.Gamma_mul_Gamma_one_sub σ

lemma cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℂ)) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

lemma pointwise (σ : ℂ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    |1 / (1 - t) ^ 2| • (((t / (1 - t) : ℝ) : ℂ) ^ (σ - 1) / (1 + ((t / (1 - t) : ℝ) : ℂ))) =
      (t : ℂ) ^ (σ - 1) * (1 - (t : ℂ)) ^ ((1 - σ) - 1) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hb : 0 < 1 - t := by linarith
  have hq : 0 < t / (1 - t) := div_pos ht0 hb
  have e1 : ((1 : ℂ) - (t : ℂ)) = (((1 - t : ℝ)) : ℂ) := by push_cast; ring
  rw [e1, abs_of_pos (by positivity : (0 : ℝ) < 1 / (1 - t) ^ 2), Complex.real_smul]
  rw [cpow_ofReal_pos hq, cpow_ofReal_pos ht0, cpow_ofReal_pos hb, Real.log_div ht0.ne' hb.ne']
  have hbne : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hden : (1 : ℂ) + ((t / (1 - t) : ℝ) : ℂ) = 1 / ((1 - t : ℝ) : ℂ) := by
    push_cast
    have : (1 : ℂ) - (t : ℂ) ≠ 0 := by simpa using hbne
    field_simp
    ring
  rw [hden]
  set L : ℂ := (Real.log (1 - t) : ℂ) with hL
  set A : ℂ := (Real.log t : ℂ) with hA
  have hE : ((1 - t : ℝ) : ℂ) = Complex.exp L := by
    rw [hL, ← Complex.ofReal_exp, Real.exp_log hb]
  have hE0 : Complex.exp L ≠ 0 := Complex.exp_ne_zero _
  have hF0 : Complex.exp (L * σ) ≠ 0 := Complex.exp_ne_zero _
  have h1 : Complex.exp (((Real.log t - Real.log (1 - t) : ℝ) : ℂ) * (σ - 1)) =
      Complex.exp (A * (σ - 1)) * Complex.exp L / Complex.exp (L * σ) := by
    push_cast
    rw [show (A - L) * (σ - 1) = A * (σ - 1) + (L - L * σ) by ring, Complex.exp_add,
      Complex.exp_sub]
    ring
  have h2 : Complex.exp (L * (1 - σ - 1)) = 1 / Complex.exp (L * σ) := by
    rw [show L * (1 - σ - 1) = -(L * σ) by ring, Complex.exp_neg, one_div]
  have h3 : (((1 / (1 - t) ^ 2 : ℝ)) : ℂ) = 1 / Complex.exp L ^ 2 := by
    push_cast
    rw [← hE]; push_cast; ring
  rw [h1, h2, h3, hE]
  field_simp

/-- **The Stieltjes–Mellin integral.** For `0 < Re σ < 1`: `∫₀^∞ x^{σ−1}/(1+x) dx = π/sin(πσ)`. -/
theorem stieltjes_mellin (σ : ℂ) (h0 : 0 < σ.re) (h1 : σ.re < 1) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (σ - 1) / (1 + (x : ℂ)) = Real.pi / Complex.sin (Real.pi * σ) := by
  rw [← beta_one_sub σ h0 h1]
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  conv_lhs => rw [← image_div_one_sub]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hasDerivWithinAt_div_one_sub
    injOn_div_one_sub]
  exact setIntegral_congr_fun measurableSet_Ioo (fun t ht => pointwise σ t ht)

/-- **The dispersion factor.** With the normalization `8π`: `8π · (π/sin(πσ)) = 8π²/sin(πσ)`. -/
theorem dispersion_factor (σ : ℂ) :
    (8 * Real.pi : ℂ) * (Real.pi / Complex.sin (Real.pi * σ)) =
      8 * (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * σ) := by
  ring

end GppStieltjesMellin
