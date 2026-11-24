/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GppVerify.RiemannHypothesis.HeartMellinSeries

/-!
# `ζ(σ) < 0` on the open unit interval (Heart claim #6 / Round 23 F9)

For every real `σ ∈ (0, 1)`, `ζ(σ)` is a negative real number. In particular `ζ` has no real zero
in `(0, 1)`.

The proof uses only Mathlib's Mellin-transform description of the completed zeta function:
`Λ(σ) = Λ₀(σ) − 1/σ − 1/(1 − σ)` with `Λ₀(σ) = ½ ∫₀^∞ x^{σ/2 − 1} F(x) dx`, where
`F = evenKernel 0 − 1` on `(1, ∞)` and `F(x) = x^{−1/2} (evenKernel 0 (1/x) − 1)` on `(0, 1)`
(the modified theta kernel). We show `0 ≤ F`, bound the integral by the elementary
dominating function `2e · e^{−x}`, so `½ ∫ ≤ e < 4 ≤ 1/σ + 1/(1 − σ)`; dividing by the positive real
`Γ_ℝ(σ) = π^{−σ/2} Γ(σ/2)` gives the sign.

No zeta zero is an input; no `sorry`, no `axiom`.
-/

namespace GppHeartZeta

open MeasureTheory Set Complex HurwitzZeta GppHeartMellin
open scoped Real

/-! ## θ₊ estimates -/

private theorem theta_summable {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ)) ^ 2 * y) := by
  have hg : Summable fun n : ℕ => Real.exp (-Real.pi * y) ^ (n + 1) := by
    have h0 : Real.exp (-Real.pi * y) < 1 := by
      have : Real.exp (-Real.pi * y) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by nlinarith [mul_pos Real.pi_pos hy])
      simpa using this
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le h0).comp_injective
      (add_left_injective 1)
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 ≤ Real.pi * y * ((n : ℝ) + 1) * n :=
    mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hy.le) (by linarith)) hn0
  nlinarith [hpos]

theorem thetaPlus_nonneg (y : ℝ) : 0 ≤ HR_thetaPlus y :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- `θ₊(y) ≤ e^{−π(y−1)} θ₊(1)` for `y ≥ 1`. -/
theorem thetaPlus_le {y : ℝ} (hy : 1 ≤ y) :
    HR_thetaPlus y ≤ Real.exp (-Real.pi * (y - 1)) * HR_thetaPlus 1 := by
  unfold HR_thetaPlus
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (theta_summable (by linarith))
    ((theta_summable one_pos).mul_left _)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    have : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
    exact_mod_cast this
  have hm2 : 1 ≤ (((n + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hy)) (sub_nonneg.mpr hm2)]

/-- `2 θ₊(y) ≤ e^{π} e^{−π y}` for `y ≥ 1`. -/
theorem two_thetaPlus_le {y : ℝ} (hy : 1 ≤ y) :
    2 * HR_thetaPlus y ≤ Real.exp Real.pi * Real.exp (-Real.pi * y) := by
  have h1 := thetaPlus_le hy
  have h2 := HR_thetaPlus_one_lt_half
  have h3 : Real.exp (-Real.pi * (y - 1)) = Real.exp Real.pi * Real.exp (-Real.pi * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h3] at h1
  have hpos : 0 < Real.exp Real.pi * Real.exp (-Real.pi * y) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2.le hpos.le]


/-! ## The modified kernel -/

open UpperHalfPlane in
/-- `evenKernel 0 y = 1 + 2 θ₊(y)` for `y > 0`. -/
theorem evenKernel_zero_eq {y : ℝ} (hy : 0 < y) :
    evenKernel 0 y = 1 + 2 * HR_thetaPlus y := by
  have h := evenKernel_def 0 y
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := by simp
  rw [h0] at h
  have hj : jacobiTheta (Complex.I * (y : ℂ)) = ((1 + 2 * HR_thetaPlus y : ℝ) : ℂ) := by
    rw [jacobiTheta_eq_tsum_nat (by simpa using hy)]
    unfold HR_thetaPlus
    rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_tsum]
    congr 2
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_exp]
    congr 1
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination ((Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (y : ℂ)) * hI
  have h2 : ((evenKernel 0 y : ℝ) : ℂ) = ((1 + 2 * HR_thetaPlus y : ℝ) : ℂ) := by
    rw [h, ← hj, jacobiTheta_eq_jacobiTheta₂]
    simp
  exact_mod_cast h2

/-- The real modified kernel: `evenKernel 0 − 1` on `(1, ∞)`, `evenKernel 0 − x^{−1/2}` on `(0, 1)`,
`0` elsewhere. -/
noncomputable def Fker (x : ℝ) : ℝ :=
  (Ioi 1).indicator (fun x => evenKernel 0 x - 1) x
    + (Ioo 0 1).indicator (fun x => evenKernel 0 x - x ^ (-(1 / 2 : ℝ))) x

theorem f_modif_eq (x : ℝ) :
    (hurwitzEvenFEPair 0).f_modif x = ((Fker x : ℝ) : ℂ) := by
  unfold WeakFEPair.f_modif Fker
  simp only [Pi.add_apply]
  by_cases h1 : x ∈ Ioi (1 : ℝ)
  · have h2 : x ∉ Ioo (0 : ℝ) 1 := fun h => by simp at h1; linarith [h.2]
    simp [indicator_of_mem h1, indicator_of_notMem h2, hurwitzEvenFEPair]
  · by_cases h2 : x ∈ Ioo (0 : ℝ) 1
    · simp [indicator_of_mem h2, indicator_of_notMem h1, hurwitzEvenFEPair]
    · simp [indicator_of_notMem h1, indicator_of_notMem h2]

theorem Fker_of_one_lt {x : ℝ} (hx : 1 < x) : Fker x = 2 * HR_thetaPlus x := by
  have h2 : x ∉ Ioo (0 : ℝ) 1 := fun h => by linarith [h.2]
  rw [Fker, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx), indicator_of_notMem h2,
    evenKernel_zero_eq (by linarith)]
  ring

theorem Fker_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Fker x = x ^ (-(1 / 2 : ℝ)) * (2 * HR_thetaPlus (1 / x)) := by
  have h1 : x ∉ Ioi (1 : ℝ) := fun h => by simp at h; linarith
  rw [Fker, indicator_of_notMem h1, indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, hx1⟩),
    zero_add]
  have hfe := evenKernel_functional_equation 0 x
  have hfe' : evenKernel 0 x = 1 / x ^ (1 / 2 : ℝ) * evenKernel 0 (1 / x) := by
    rw [hfe, evenKernel_eq_cosKernel_of_zero]
  rw [hfe', evenKernel_zero_eq (by positivity), Real.rpow_neg hx0.le]
  field_simp
  ring

theorem Fker_nonneg (x : ℝ) : 0 ≤ Fker x := by
  rcases lt_trichotomy x 1 with h | h | h
  · rcases le_or_gt x 0 with h0 | h0
    · simp [Fker, indicator_of_notMem (show x ∉ Ioi (1 : ℝ) by simp; linarith),
        indicator_of_notMem (show x ∉ Ioo (0 : ℝ) 1 by simp; intro; linarith)]
    · rw [Fker_of_lt_one h0 h]
      have := thetaPlus_nonneg (1 / x)
      positivity
  · subst h; simp [Fker]
  · rw [Fker_of_one_lt h]
    have := thetaPlus_nonneg x
    positivity


/-! ## Domination and the integral bound -/

/-- Dominating function: `x^{σ/2 − 1} F(x) ≤ 2e · e^{−x}` for `x > 0`, `0 < σ < 1`. -/
theorem integrand_le {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hx : 0 < x) :
    x ^ (σ / 2 - 1) * Fker x ≤ 2 * Real.exp 1 * Real.exp (-x) := by
  have hE : 2 * Real.exp 1 * Real.exp (-x) = 2 * Real.exp (1 - x) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2
  rw [hE]
  rcases lt_trichotomy x 1 with h | h | h
  · -- 0 < x < 1
    have hy : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
    rw [Fker_of_lt_one hx h]
    set y : ℝ := 1 / x with hydef
    have hxy : x⁻¹ = y := by rw [hydef, one_div]
    have ha : x ^ (σ / 2 - 1) ≤ y := by
      calc x ^ (σ / 2 - 1) ≤ x ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hx h.le (by linarith)
        _ = y := by rw [Real.rpow_neg_one, hxy]
    have hb : x ^ (-(1 / 2 : ℝ)) ≤ y := by
      calc x ^ (-(1 / 2 : ℝ)) ≤ x ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hx h.le (by linarith)
        _ = y := by rw [Real.rpow_neg_one, hxy]
    have hθ := two_thetaPlus_le hy
    have hθ0 := thetaPlus_nonneg y
    have hb0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
    have hy0 : 0 ≤ y := by linarith
    have hab : x ^ (σ / 2 - 1) * x ^ (-(1 / 2 : ℝ)) ≤ y * y :=
      mul_le_mul ha hb hb0 hy0
    have hq : y * y * (Real.exp Real.pi * Real.exp (-Real.pi * y)) ≤ 2 := by
      have e1 : Real.exp Real.pi * Real.exp (-Real.pi * y) = Real.exp (-(Real.pi * (y - 1))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e1, Real.exp_neg, ← div_eq_mul_inv]
      have ht : 0 ≤ Real.pi * (y - 1) := mul_nonneg Real.pi_pos.le (by linarith)
      have hq := Real.quadratic_le_exp_of_nonneg ht
      have hpos : 0 < Real.exp (Real.pi * (y - 1)) := Real.exp_pos _
      rw [div_le_iff₀ hpos]
      have hp3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have ht0 : 0 ≤ y - 1 := by linarith
      nlinarith [mul_nonneg ht0 ht0, mul_nonneg ht0 (sub_nonneg.mpr hp3.le)]
    have h1 : 1 ≤ Real.exp (1 - x) := Real.one_le_exp (by linarith)
    calc x ^ (σ / 2 - 1) * (x ^ (-(1 / 2 : ℝ)) * (2 * HR_thetaPlus y))
        = (x ^ (σ / 2 - 1) * x ^ (-(1 / 2 : ℝ))) * (2 * HR_thetaPlus y) := by ring
      _ ≤ (y * y) * (2 * HR_thetaPlus y) :=
          mul_le_mul_of_nonneg_right hab (by linarith)
      _ ≤ y * y * (Real.exp Real.pi * Real.exp (-Real.pi * y)) :=
          mul_le_mul_of_nonneg_left hθ (by positivity)
      _ ≤ 2 := hq
      _ ≤ 2 * Real.exp (1 - x) := by linarith
  · subst h
    simp [Fker]
  · -- x > 1
    rw [Fker_of_one_lt h]
    have hw : x ^ (σ / 2 - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    have hθ := two_thetaPlus_le h.le
    have hθ0 : 0 ≤ 2 * HR_thetaPlus x := by linarith [thetaPlus_nonneg x]
    have e1 : Real.exp Real.pi * Real.exp (-Real.pi * x) = Real.exp (-(Real.pi * (x - 1))) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(Real.pi * (x - 1))) ≤ Real.exp (1 - x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    have hpos : 0 < Real.exp (1 - x) := Real.exp_pos _
    calc x ^ (σ / 2 - 1) * (2 * HR_thetaPlus x) ≤ 1 * (2 * HR_thetaPlus x) :=
          mul_le_mul_of_nonneg_right hw hθ0
      _ ≤ Real.exp Real.pi * Real.exp (-Real.pi * x) := by linarith
      _ ≤ Real.exp (1 - x) := by rw [e1]; exact e2
      _ ≤ 2 * Real.exp (1 - x) := by linarith

theorem integral_Fker_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∫ x in Ioi (0 : ℝ), x ^ (σ / 2 - 1) * Fker x ≤ 2 * Real.exp 1 := by
  have hint : Integrable (fun x : ℝ => 2 * Real.exp 1 * Real.exp (-x))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (2 * Real.exp 1)
    simpa using this
  have hval : ∫ x in Ioi (0 : ℝ), 2 * Real.exp 1 * Real.exp (-x) = 2 * Real.exp 1 := by
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [← hval]
  refine integral_mono_of_nonneg ?_ hint ?_
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Fker_nonneg x)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    exact integrand_le hσ0 hσ1 hx

/-- The completed zeta function at a real point of `(0, 1)` is the explicit real number
`½ ∫₀^∞ x^{σ/2 − 1} F(x) dx − 1/σ − 1/(1 − σ)` (valid for every real `σ`). -/
theorem completedRiemannZeta_ofReal (σ : ℝ) :
    completedRiemannZeta (σ : ℂ)
      = ((((∫ x in Ioi (0 : ℝ), x ^ (σ / 2 - 1) * Fker x) / 2 - 1 / σ - 1 / (1 - σ) : ℝ)) : ℂ) := by
  rw [completedRiemannZeta_eq]
  have hM : completedRiemannZeta₀ (σ : ℂ)
      = (((∫ x in Ioi (0 : ℝ), x ^ (σ / 2 - 1) * Fker x) / 2 : ℝ) : ℂ) := by
    unfold completedRiemannZeta₀ completedHurwitzZetaEven₀ WeakFEPair.Λ₀ mellin
    have hcongr : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((σ : ℂ) / 2 - 1) • (hurwitzEvenFEPair 0).f_modif t
        = ∫ t in Ioi (0 : ℝ), (((t ^ (σ / 2 - 1) * Fker t : ℝ)) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 ≤ t := le_of_lt ht
      simp only [f_modif_eq, smul_eq_mul]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0]
      push_cast
      ring_nf
    rw [hcongr, integral_complex_ofReal]
    push_cast
    ring
  have hσc : (1 : ℂ) / σ = ((1 / σ : ℝ) : ℂ) := by push_cast; rfl
  have hσc' : (1 : ℂ) / (1 - σ) = ((1 / (1 - σ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hM, hσc, hσc']
  push_cast
  ring

/-- Auxiliary: `Γ_ℝ(σ)` is a positive real for `σ > 0`. -/
theorem Gammaℝ_ofReal_pos {σ : ℝ} (hσ : 0 < σ) :
    ∃ g : ℝ, 0 < g ∧ Complex.Gammaℝ (σ : ℂ) = (g : ℂ) := by
  refine ⟨Real.pi ^ (-σ / 2) * Real.Gamma (σ / 2),
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith)), ?_⟩
  rw [Complex.Gammaℝ_def, Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le]
  have h1 : (-(σ : ℂ) / 2) = ((-σ / 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((σ : ℂ) / 2) = ((σ / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.Gamma_ofReal]

/-- **Heart claim #6 / F9.** For `σ ∈ (0, 1)`, `ζ(σ)` is a negative real number. -/
theorem riemannZeta_real_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ r : ℝ, r < 0 ∧ riemannZeta (σ : ℂ) = (r : ℂ) := by
  obtain ⟨g, hg, hGam⟩ := Gammaℝ_ofReal_pos hσ0
  have hσne : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hM := integral_Fker_le hσ0 hσ1
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h4 : 4 ≤ 1 / σ + 1 / (1 - σ) := by
    have h1 : 0 < 1 - σ := by linarith
    rw [div_add_div _ _ hσ0.ne' h1.ne', le_div_iff₀ (mul_pos hσ0 h1)]
    nlinarith [sq_nonneg (σ - 1 / 2)]
  set M := ∫ x in Ioi (0 : ℝ), x ^ (σ / 2 - 1) * Fker x with hMdef
  have hneg : M / 2 - 1 / σ - 1 / (1 - σ) < 0 := by linarith
  refine ⟨(M / 2 - 1 / σ - 1 / (1 - σ)) / g, div_neg_of_neg_of_pos hneg hg, ?_⟩
  rw [riemannZeta_def_of_ne_zero hσne, completedRiemannZeta_ofReal σ, hGam]
  push_cast
  rfl

/-- `Re ζ(σ) < 0` and `Im ζ(σ) = 0` on `(0, 1)`. -/
theorem riemannZeta_re_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 ∧ (riemannZeta (σ : ℂ)).im = 0 := by
  obtain ⟨r, hr, h⟩ := riemannZeta_real_neg hσ0 hσ1
  rw [h]
  simpa using hr

/-- `ζ` has no real zero in `(0, 1)`. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro h
  have := (riemannZeta_re_neg hσ0 hσ1).1
  rw [h] at this
  simp at this

end GppHeartZeta

#print axioms GppHeartZeta.riemannZeta_real_neg
#print axioms GppHeartZeta.riemannZeta_re_neg
#print axioms GppHeartZeta.riemannZeta_ne_zero_of_mem_Ioo
