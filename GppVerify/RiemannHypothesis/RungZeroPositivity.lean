import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import GppVerify.RiemannHypothesis.AutocorrTransport
import GppVerify.RiemannHypothesis.DigammaIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Unconditional Weil positivity on a small window

**Main theorem** (`reflectionPositiveOnRung_one_div_128`): `ReflectionPositiveOnRung (1/128)`.
For every smooth compactly supported `f` vanishing outside `[-1/256, 1/256]`,

  `0 ≤ weilForm (autocorr f)`.

In fact `weilForm (autocorr f) ≥ (3/10) · ∫ f²` (`weilForm_autocorr_ge`). This is a theorem
with no named premises. It is the first proved instance of `ReflectionPositiveOnRung L` for any
`L > 0`. The window is far below the first prime (`log 2`), so no prime enters. The content is
that the pole term and the archimedean term already dominate there. It says nothing about the
zeros.

## Proof

Write `a = autocorr f` and `a₀ = a(0) = ∫ f²`.

1. `|a(u)| ≤ a₀` (`abs_autocorr_le`), by pointwise AM-GM and translation invariance.
2. **Archimedean term.** Normalise `r = a / a₀`. The in-tree decomposition gives
   `A∞ = C∞ + 2 · Dirichlet form`, with `C∞ = -γ - log π - π/2 - 3 log 2`. The Dirichlet
   integrand is nonnegative, and it equals `e^{-u/2}/(1 - e^{-2u})` beyond the support.
   With elementary bounds,
   `2 ∫_{1/128}^∞ e^{-u/2}/(1 - e^{-2u}) du ≥ 8 log 2 - (2 - 1/128)/2 + 4/e`.
   The integrability of the real-place integrand, which `archimedean_floor` takes as a
   hypothesis, is proved here for every test function (`integrableOn_archimedeanIntegrand`),
   from a Lipschitz bound.
3. **Pole term.** `∫ a · 2cosh(u/2) = 2 (∫ f)² + ∫ a · (2cosh(u/2) - 2)`. The first piece is
   `≥ 0`, and the second is at most `a₀ · 2L · 2(e - 1)` in absolute value.
4. **Arithmetic.**
   `-γ - log π - π/2 - 3 log 2 + 8 log 2 - (2 - 1/128)/2 + 4/e - (1/64)(e - 1) ≥ 3/10`,
   using `γ < 2/3`, `log π ≤ log 2 + π/2 - 1`, `π < 3.15`, Mathlib's nine-digit bounds on
   `log 2`, and `e < 2.7182818286`.

Unconditional. No `sorry`, no axioms beyond Lean's standard three.
-/

namespace GppRungZeroPositivity

open Real MeasureTheory Set Filter GppArchimedeanFloor GppArithmeticReflection GppWeilLadder
  GppMeyerSpectralWeil
open scoped ContDiff

/-! ## Integrability of the real-place integrand for a test function -/

/-- A smooth compactly supported function is Lipschitz. -/
theorem exists_lipschitz {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : ℝ, |g x - g y| ≤ M * |x - y| := by
  have hd : Continuous (deriv g) := hg.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hc.deriv.exists_bound_of_continuous hd
  refine ⟨max C 0, le_max_right _ _, fun x y => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := g) (C := max C 0)
    (fun z _ => (hg.differentiable (by simp)).differentiableAt)
    (fun z _ => (hC z).trans (le_max_left _ _)) convex_univ (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- `1 - e^{-2u} ≥ 2u/(1 + 2u)` for `u ≥ 0`. -/
theorem one_sub_exp_neg_two_mul_ge {u : ℝ} (hu : 0 ≤ u) :
    2 * u / (1 + 2 * u) ≤ 1 - Real.exp (-2 * u) := by
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hpos : 0 < 1 + 2 * u := by linarith
  have he : Real.exp (-2 * u) = (Real.exp (2 * u))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [he]
  have hinv : (Real.exp (2 * u))⁻¹ ≤ (1 + 2 * u)⁻¹ := inv_anti₀ hpos h1
  have : 2 * u / (1 + 2 * u) = 1 - (1 + 2 * u)⁻¹ := by field_simp; ring
  rw [this]; linarith

/-- The translation part of the real-place integrand. -/
noncomputable def transIntegrand (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (-u / 2) * (g 0 - g u) / (1 - Real.exp (-2 * u))

theorem archimedeanIntegrand_eq (g : ℝ → ℝ) (u : ℝ) :
    archimedeanIntegrand g u = g 0 * (constKernel u / 2) + transIntegrand g u := by
  unfold archimedeanIntegrand constKernel transIntegrand
  ring

theorem integrableOn_transIntegrand {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    IntegrableOn (transIntegrand g) (Ioi 0) := by
  obtain ⟨M, hM, hL⟩ := exists_lipschitz hg hc
  have hbound : IntegrableOn (fun u : ℝ => (M / 2) * (Real.exp (-(1 / 2) * u) +
      2 * (u * Real.exp (-(1 / 2) * u)))) (Ioi 0) := by
    have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(1 / 2) * u)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by norm_num)
    have h2 : IntegrableOn (fun u : ℝ => u * Real.exp (-(1 / 2) * u)) (Ioi 0) := by
      exact GppDigammaIntegral.integrableOn_t_exp (by norm_num)
    exact ((h1.add (h2.const_mul 2)).const_mul (M / 2))
  have hcont : ContinuousOn (transIntegrand g) (Ioi 0) := by
    have hgc : Continuous g := hg.continuous
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun u hu => ?_)
    have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by simp at hu; linarith)
    linarith
  refine hbound.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  have hu : (0 : ℝ) < u := hu
  have hden : 2 * u / (1 + 2 * u) ≤ 1 - Real.exp (-2 * u) := one_sub_exp_neg_two_mul_ge hu.le
  have hdpos : 0 < 2 * u / (1 + 2 * u) := by positivity
  have hlip : |g 0 - g u| ≤ M * u := by
    have := hL 0 u; rwa [zero_sub, abs_neg, abs_of_pos hu] at this
  have he : 0 < Real.exp (-u / 2) := Real.exp_pos _
  have hexp : Real.exp (-u / 2) = Real.exp (-(1 / 2) * u) := by ring_nf
  rw [Real.norm_eq_abs]
  unfold transIntegrand
  rw [abs_div, abs_mul, abs_of_pos he, abs_of_pos (lt_of_lt_of_le hdpos hden)]
  calc Real.exp (-u / 2) * |g 0 - g u| / (1 - Real.exp (-2 * u))
      ≤ Real.exp (-u / 2) * (M * u) / (2 * u / (1 + 2 * u)) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hlip he.le) hdpos hden
    _ = (M / 2) * (Real.exp (-(1 / 2) * u) + 2 * (u * Real.exp (-(1 / 2) * u))) := by
        rw [hexp]; field_simp

/-- **The real-place integrand of a test function is integrable.** -/
theorem integrableOn_archimedeanIntegrand {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : IntegrableOn (archimedeanIntegrand g) (Ioi 0) := by
  have h : IntegrableOn (fun u => g 0 * (constKernel u / 2) + transIntegrand g u) (Ioi 0) :=
    ((integrableOn_constKernel.div_const 2).const_mul (g 0)).add
      (integrableOn_transIntegrand hg hc)
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  rw [archimedeanIntegrand_eq]

/-! ## Autocorrelation facts -/

theorem integrable_mul_shift {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : ℝ) : Integrable (fun y => f y * f (y - u)) :=
  (hf.continuous.mul (hf.continuous.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    (hc.mul_right)

theorem integrable_sq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun y => f y ^ 2) :=
  (integrable_mul_shift hf hc 0).congr (Filter.Eventually.of_forall fun y => by
    simp only [sub_zero]; ring)

theorem integrable_sq_shift {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : ℝ) : Integrable (fun y => f (y - u) ^ 2) :=
  (integrable_sq hf hc).comp_sub_right u

theorem autocorr_zero_eq (f : ℝ → ℝ) : autocorr f 0 = ∫ y, f y ^ 2 := by
  unfold autocorr; congr 1; funext y; rw [sub_zero]; ring

/-- **`|a(u)| ≤ a(0)`.** -/
theorem abs_autocorr_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (u : ℝ) :
    |autocorr f u| ≤ autocorr f 0 := by
  have hsq := integrable_sq hf hc
  have hsh := integrable_sq_shift hf hc u
  have htr : ∫ y, f (y - u) ^ 2 = ∫ y, f y ^ 2 :=
    integral_sub_right_eq_self (fun y => f y ^ 2) u
  have hbound : ∀ y, |f y * f (y - u)| ≤ (f y ^ 2 + f (y - u) ^ 2) / 2 := by
    intro y
    rw [abs_mul]
    nlinarith [sq_nonneg (|f y| - |f (y - u)|), sq_abs (f y), sq_abs (f (y - u))]
  have h1 : |autocorr f u| ≤ ∫ y, (f y ^ 2 + f (y - u) ^ 2) / 2 := by
    unfold autocorr
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hsq.add hsh).div_const 2)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hbound y
  rw [integral_div, integral_add hsq hsh, htr] at h1
  rw [autocorr_zero_eq]
  linarith

theorem autocorr_zero_nonneg (f : ℝ → ℝ) : 0 ≤ autocorr f 0 := by
  rw [autocorr_zero_eq]; exact integral_nonneg (fun y => sq_nonneg _)

/-- **`∫ a = (∫ f)²`**, from the in-tree transform identity at `s = 1/2`. -/
theorem integral_autocorr {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∫ u, autocorr f u = (∫ y, f y) ^ 2 := by
  have h := GppAutocorrTransport.spectralTransform_autocorr (g := f) ⟨hf, hc⟩ (1 / 2)
  unfold spectralTransform at h
  simp only [sub_self, zero_mul, Complex.exp_zero, mul_one] at h
  norm_num at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at this
  rw [this]; ring

/-! ## The real-place kernel beyond the support -/

/-- The Dirichlet kernel `e^{-u/2} / (1 - e^{-2u})`. -/
noncomputable def kern (u : ℝ) : ℝ := Real.exp (-u / 2) / (1 - Real.exp (-2 * u))

theorem one_sub_exp_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-2 * u) := by
  have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem one_sub_exp_le {u : ℝ} : 1 - Real.exp (-2 * u) ≤ 2 * u := by
  linarith [Real.add_one_le_exp (-2 * u)]

theorem kern_ge_exp {u : ℝ} (hu : 0 < u) : Real.exp (-(1 / 2) * u) ≤ kern u := by
  unfold kern
  have hd := one_sub_exp_pos hu
  have hd1 : 1 - Real.exp (-2 * u) ≤ 1 := by linarith [Real.exp_pos (-2 * u)]
  rw [le_div_iff₀ hd]
  have he : Real.exp (-(1 / 2) * u) = Real.exp (-u / 2) := by ring_nf
  rw [he]
  nlinarith [Real.exp_pos (-u / 2)]

theorem kern_ge_near {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) : u⁻¹ * (1 / 2) - 1 / 4 ≤ kern u := by
  unfold kern
  have hd := one_sub_exp_pos hu
  have hle := one_sub_exp_le (u := u)
  have hexp : 1 - u / 2 ≤ Real.exp (-u / 2) := by linarith [Real.add_one_le_exp (-u / 2)]
  have h1 : (1 - u / 2) / (2 * u) ≤ (1 - u / 2) / (1 - Real.exp (-2 * u)) :=
    div_le_div_of_nonneg_left (by linarith) hd hle
  have h2 : (1 - u / 2) / (1 - Real.exp (-2 * u)) ≤ Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) :=
    div_le_div_of_nonneg_right hexp hd.le
  have h3 : u⁻¹ * (1 / 2) - 1 / 4 = (1 - u / 2) / (2 * u) := by field_simp; ring
  linarith

theorem kern_continuousOn : ContinuousOn kern (Ioi 0) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun u hu => (one_sub_exp_pos hu).ne')

theorem integrableOn_kern {L : ℝ} (hL : 0 < L) : IntegrableOn kern (Ioi L) := by
  have hdL := one_sub_exp_pos hL
  have hb : IntegrableOn (fun u : ℝ => Real.exp (-(1 / 2) * u) / (1 - Real.exp (-2 * L))) (Ioi L) :=
    (exp_neg_integrableOn_Ioi L (by norm_num)).div_const _
  refine hb.mono' ((kern_continuousOn.mono (Ioi_subset_Ioi hL.le)).aestronglyMeasurable
    measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  have hu : L < u := hu
  have hu0 : 0 < u := hL.trans hu
  have hd := one_sub_exp_pos hu0
  have hmono : 1 - Real.exp (-2 * L) ≤ 1 - Real.exp (-2 * u) := by
    have := Real.exp_le_exp.mpr (by linarith : -2 * u ≤ -2 * L); linarith
  unfold kern
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hd)]
  have he : Real.exp (-u / 2) = Real.exp (-(1 / 2) * u) := by ring_nf
  rw [he]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hdL hmono

/-- **The tail of the Dirichlet kernel.** For `0 < L ≤ 2`,
`2 ∫_L^∞ e^{-u/2}/(1 - e^{-2u}) du ≥ log(2/L) - (2 - L)/2 + 4/e`. -/
theorem two_mul_integral_kern_ge {L : ℝ} (hL : 0 < L) (hL2 : L ≤ 2) :
    Real.log (2 / L) - (2 - L) / 2 + 4 * Real.exp (-1) ≤ 2 * ∫ u in Ioi L, kern u := by
  have hsplit : Ioi L = Ioc L 2 ∪ Ioi 2 := (Ioc_union_Ioi_eq_Ioi hL2).symm
  have hint := integrableOn_kern hL
  have h1 : IntegrableOn kern (Ioc L 2) := hint.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn kern (Ioi 2) := hint.mono_set (Ioi_subset_Ioi hL2)
  have hU : ∫ u in Ioi L, kern u = (∫ u in Ioc L 2, kern u) + ∫ u in Ioi 2, kern u := by
    rw [hsplit]; exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2
  -- near piece
  have hnearInt : IntervalIntegrable (fun u : ℝ => u⁻¹ * (1 / 2) - 1 / 4) volume L 2 := by
    refine ((intervalIntegral.intervalIntegrable_inv (f := fun u => u) (fun x hx => ?_)
      continuousOn_id).mul_const _).sub intervalIntegrable_const
    rw [uIcc_of_le hL2] at hx; exact (hL.trans_le hx.1).ne'
  have hnear : (Real.log (2 / L)) / 2 - (2 - L) / 4 ≤ ∫ u in Ioc L 2, kern u := by
    have hval : ∫ u in Ioc L 2, (u⁻¹ * (1 / 2) - 1 / 4) = (Real.log (2 / L)) / 2 - (2 - L) / 4 := by
      rw [← intervalIntegral.integral_of_le hL2, intervalIntegral.integral_sub
        ((intervalIntegral.intervalIntegrable_inv (f := fun u => u) (fun x hx => ?_)
          continuousOn_id).mul_const _) intervalIntegrable_const,
        intervalIntegral.integral_mul_const, integral_inv_of_pos hL (by norm_num),
        intervalIntegral.integral_const, smul_eq_mul]
      · ring
      · rw [uIcc_of_le hL2] at hx; exact (hL.trans_le hx.1).ne'
    rw [← hval]
    refine setIntegral_mono_on ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL2).mp hnearInt)
      h1 measurableSet_Ioc (fun u hu => kern_ge_near (hL.trans hu.1) hu.2)
  -- far piece
  have hfar : 2 * Real.exp (-1) ≤ ∫ u in Ioi 2, kern u := by
    have hval : ∫ u in Ioi (2 : ℝ), Real.exp (-(1 / 2) * u) = 2 * Real.exp (-1) := by
      rw [integral_exp_mul_Ioi (by norm_num) 2]; ring_nf
    rw [← hval]
    exact setIntegral_mono_on (exp_neg_integrableOn_Ioi 2 (by norm_num)) h2 measurableSet_Ioi
      (fun u hu => kern_ge_exp (by simp at hu; linarith))
  rw [hU]
  linarith

/-! ## The archimedean term of a small-window autocorrelation -/

/-- **Archimedean bound.** If `a = autocorr f` vanishes outside `[-L, L]`, `0 < L ≤ 2`, then
`A∞(a) ≥ a(0) (C∞ + log(2/L) - (2 - L)/2 + 4/e)`. -/
theorem archimedeanTerm_autocorr_ge {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {L : ℝ} (hL : 0 < L) (hL2 : L ≤ 2) (hsupp : HasSupportIn (autocorr f) L) :
    autocorr f 0 * (archimedeanFloor + (Real.log (2 / L) - (2 - L) / 2 + 4 * Real.exp (-1)))
      ≤ archimedeanTerm (autocorr f) := by
  set a := autocorr f with ha_def
  have hta : IsTestFunction a := GppAutocorrTransport.isTestFunction_autocorr ⟨hf, hc⟩
  have ha0 := autocorr_zero_nonneg f
  rcases ha0.lt_or_eq with hpos | hzero
  · set r : ℝ → ℝ := fun u => a u / a 0 with hr
    have hr0 : r 0 = 1 := by simp only [hr]; exact div_self hpos.ne'
    have hrle : ∀ u, r u ≤ 1 := by
      intro u; simp only [hr]
      rw [div_le_one hpos]; exact (le_abs_self _).trans (abs_autocorr_le hf hc u)
    have hscale : ∀ u, archimedeanIntegrand a u = a 0 * archimedeanIntegrand r u := by
      intro u; unfold archimedeanIntegrand; simp only [hr]; field_simp
      rw [mul_div_mul_left _ _ hpos.ne']
    have hintA := integrableOn_archimedeanIntegrand hta.1 hta.2
    have hintR : IntegrableOn (archimedeanIntegrand r) (Ioi 0) := by
      have h' : IntegrableOn (fun u => archimedeanIntegrand a u / a 0) (Ioi 0) :=
        hintA.div_const _
      refine h'.congr_fun (fun u _ => ?_) measurableSet_Ioi
      show archimedeanIntegrand a u / a 0 = archimedeanIntegrand r u
      rw [hscale, mul_div_cancel_left₀ _ hpos.ne']
    have harch : archimedeanTerm a = a 0 * archimedeanTerm r := by
      unfold archimedeanTerm
      simp only [hscale, integral_const_mul, hr0]
      simp only [hr]; field_simp
    have hdec := archimedean_decomposition r hr0 hintR
    -- Dirichlet form ≥ tail
    have hdint : IntegrableOn (dirichletIntegrand r) (Ioi 0) := by
      refine (hintR.sub (integrableOn_constKernel.div_const 2)).congr_fun (fun u _ => ?_)
        measurableSet_Ioi
      simp only [Pi.sub_apply, archimedeanIntegrand_split r hr0 u]; ring
    have hdnn : ∀ u, 0 < u → 0 ≤ dirichletIntegrand r u := by
      intro u hu
      unfold dirichletIntegrand
      have := hrle u
      have := one_sub_exp_pos hu
      have : 0 ≤ 1 - r u := by linarith
      positivity
    have htail : ∫ u in Ioi L, kern u ≤ dirichletForm r := by
      have heq : ∫ u in Ioi L, dirichletIntegrand r u = ∫ u in Ioi L, kern u := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        have hu : L < u := hu
        have hz : a u = 0 := hsupp u (by rw [abs_of_pos (hL.trans hu)]; exact hu)
        unfold dirichletIntegrand kern
        simp only [hr, hz, zero_div, sub_zero, mul_one]
      rw [← heq]
      exact setIntegral_mono_set hdint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hdnn))
        (Filter.Eventually.of_forall (fun u hu => Ioi_subset_Ioi hL.le hu))
    have hk := two_mul_integral_kern_ge hL hL2
    rw [harch, hdec]
    have : archimedeanFloor + (Real.log (2 / L) - (2 - L) / 2 + 4 * Real.exp (-1))
        ≤ archimedeanFloor + 2 * dirichletForm r := by linarith
    exact mul_le_mul_of_nonneg_left this hpos.le
  · -- a ≡ 0
    have hzero' : ∀ u, a u = 0 := fun u => by
      have := abs_autocorr_le hf hc u
      rw [← hzero] at this
      exact abs_nonpos_iff.mp this
    have : archimedeanTerm a = 0 := by
      unfold archimedeanTerm archimedeanIntegrand; simp [hzero']
    have h0 : a 0 = 0 := hzero.symm
    rw [this, h0, zero_mul]

/-! ## The pole term -/

theorem abs_two_cosh_sub_two_le {u : ℝ} (hu : |u| ≤ 2) :
    |2 * Real.cosh (u / 2) - 2| ≤ 2 * (Real.exp 1 - 1) := by
  have h1 := Real.one_le_cosh (u / 2)
  have h2 : Real.cosh (u / 2) ≤ Real.exp 1 := by
    refine (Real.cosh_le_exp_half_sq (u / 2)).trans (Real.exp_le_exp.mpr ?_)
    have : u ^ 2 ≤ 4 := by nlinarith [abs_nonneg u, sq_abs u]
    nlinarith
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Pole bound.** If `a = autocorr f` vanishes outside `[-L, L]`, `0 < L ≤ 2`, then
`poleTerm a ≥ -4L(e - 1) a(0)`. -/
theorem poleTerm_autocorr_ge {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {L : ℝ} (hL : 0 < L) (hL2 : L ≤ 2) (hsupp : HasSupportIn (autocorr f) L) :
    -(4 * L * (Real.exp 1 - 1)) * autocorr f 0 ≤ poleTerm (autocorr f) := by
  set a := autocorr f with ha_def
  have hta : IsTestFunction a := GppAutocorrTransport.isTestFunction_autocorr ⟨hf, hc⟩
  have hac : Continuous a := hta.1.continuous
  have haint : Integrable a := hac.integrable_of_hasCompactSupport hta.2
  have hcosh : Integrable (fun u => a u * (2 * Real.cosh (u / 2) - 2)) :=
    (hac.mul (by fun_prop)).integrable_of_hasCompactSupport hta.2.mul_right
  set c : ℝ := a 0 * (2 * (Real.exp 1 - 1)) with hc_def
  have hbound : ∀ u, ‖a u * (2 * Real.cosh (u / 2) - 2)‖ ≤ (Icc (-L) L).indicator (fun _ => c) u := by
    intro u
    by_cases hu : u ∈ Icc (-L) L
    · rw [indicator_of_mem hu, Real.norm_eq_abs, abs_mul]
      have hu' : |u| ≤ 2 := (abs_le.mpr hu).trans hL2
      exact mul_le_mul (abs_autocorr_le hf hc u) (abs_two_cosh_sub_two_le hu') (abs_nonneg _)
        (autocorr_zero_nonneg f)
    · rw [indicator_of_notMem hu]
      have : L < |u| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hu
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      simp [hsupp u this]
  have hind : Integrable ((Icc (-L) L).indicator (fun _ => c)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hnorm := norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hbound)
  rw [integral_indicator_const c measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul, Real.norm_eq_abs] at hnorm
  have hsplit : poleTerm a = 2 * (∫ u, a u) + ∫ u, a u * (2 * Real.cosh (u / 2) - 2) := by
    unfold poleTerm
    rw [← integral_const_mul, ← integral_add (haint.const_mul 2) hcosh]
    congr 1; funext u; ring
  have hsq : 0 ≤ ∫ u, a u := by rw [ha_def, integral_autocorr hf hc]; exact sq_nonneg _
  have := neg_abs_le (∫ u, a u * (2 * Real.cosh (u / 2) - 2))
  rw [hsplit]
  have e : (L - -L) * c = 4 * L * (Real.exp 1 - 1) * a 0 := by rw [hc_def]; ring
  rw [e] at hnorm
  linarith

/-! ## Numerics -/

theorem numeric_margin :
    3 / 10 ≤ archimedeanFloor + (Real.log (2 / (1 / 128)) - (2 - 1 / 128) / 2
      + 4 * Real.exp (-1)) - 4 * (1 / 128) * (Real.exp 1 - 1) := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_one_gt_d9
  -- log π ≤ log 2 + (π/2 - 1)
  have hlogpi : Real.log Real.pi ≤ Real.log 2 + (Real.pi / 2 - 1) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.pi / 2)
    rw [Real.log_div hpi0.ne' (by norm_num)] at h
    linarith
  have h256 : Real.log (2 / (1 / 128)) = 8 * Real.log 2 := by
    rw [show (2 : ℝ) / (1 / 128) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have hinv : 4 * Real.exp (-1) = 4 / Real.exp 1 := by rw [Real.exp_neg]; ring
  have hdiv : 4 / (2.7182818286 : ℝ) ≤ 4 / Real.exp 1 :=
    div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos 1) he.le
  rw [h256, hinv]
  unfold archimedeanFloor
  norm_num at hdiv ⊢
  linarith

/-! ## The theorem -/

/-- **Unconditional Weil positivity on `[-1/256, 1/256]`, quantitative.** -/
theorem weilForm_autocorr_ge {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hsupp : ∀ y : ℝ, (1 / 128 : ℝ) / 2 < |y| → f y = 0) :
    (3 / 10) * ∫ y, f y ^ 2 ≤ weilForm (autocorr f) := by
  have hL : (1 / 128 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [weilForm_rung_zero hsupp hL]
  have hs := autocorr_hasSupportIn hsupp
  have harch := archimedeanTerm_autocorr_ge hf hc (by norm_num) (by norm_num) hs
  have hpole := poleTerm_autocorr_ge hf hc (by norm_num) (by norm_num) hs
  have hm := numeric_margin
  have ha0 := autocorr_zero_nonneg f
  rw [← autocorr_zero_eq]
  nlinarith [mul_le_mul_of_nonneg_left hm ha0]

/-- **`ReflectionPositiveOnRung (1/128)`: the first proved rung.** -/
theorem reflectionPositiveOnRung_one_div_128 : ReflectionPositiveOnRung (1 / 128) := by
  intro f hf hc hsupp
  have h := weilForm_autocorr_ge hf hc hsupp
  have : 0 ≤ (3 / 10) * ∫ y, f y ^ 2 :=
    mul_nonneg (by norm_num) (integral_nonneg fun y => sq_nonneg _)
  linarith

/-- Every smaller window follows. -/
theorem reflectionPositiveOnRung_of_le {L : ℝ} (hL : L ≤ 1 / 128) : ReflectionPositiveOnRung L := by
  intro f hf hc hsupp
  exact reflectionPositiveOnRung_one_div_128 f hf hc
    (fun y hy => hsupp y (lt_of_le_of_lt (by linarith) hy))

end GppRungZeroPositivity
