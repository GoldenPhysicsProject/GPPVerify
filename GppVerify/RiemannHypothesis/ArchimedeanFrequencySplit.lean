import GppVerify.RiemannHypothesis.ArchimedeanIdentification
import GppVerify.RiemannHypothesis.AutocorrTransport
import GppVerify.RiemannHypothesis.DigammaVerticalFloor
import GppVerify.RiemannHypothesis.DigammaQuarterSech

/-!
# The archimedean term of an autocorrelation, split in frequency

Let `g` be a real test function, `a = autocorr g` and `h(r) = ĝ(1/2 + i r)`. This module proves:

* `hline_autocorr`: `ĥ_a(r) = |h(r)|²`. The transform of the autocorrelation is real and
  nonnegative on the critical line.
* `archimedeanTerm_autocorr_eq`:
  `archimedeanTerm a = (1/2π) ∫ |h(r)|² (Re ψ(1/4 + i r/2) - log π) dr`.
* `archimedeanTerm_autocorr_ge`: for `T ≥ 2`, with `c_T = log(T/(2π)) - 1/T`,

    `archimedeanTerm a ≥ c_T · a(0) + (1/2π) ∫_{-T}^{T} |h|² (Re ψ - log π - c_T) dr`.

  The digamma floor `DigammaVerticalFloor.re_digamma_quarter_ge` makes the integrand
  nonnegative for `|r| ≥ T`, so dropping that range only lowers the right-hand side.

This is the archimedean half of piece (a), the frequency form, in the rung-1 Lean plan
(`GPP-bridge/work/claude-code/rung1/STEP0-REPRODUCTION-2026-11-13.md`). It replaces the
archimedean symbol on `|r| ≥ T` by the constant `c_T`, exactly as the one-stroke certificate
does. The prime half (the cosine sum) and the pole half are separate pieces.

Unconditional. No `sorry`, no axioms, no named premises. Nothing here concerns the zeros.
-/

namespace GppArchimedeanFrequencySplit

open Complex Set MeasureTheory GppMeyerSpectralWeil GppArchimedeanId GppAutocorrTransport
  GppArithmeticReflection

/-- The critical-line point `z_r = 1/4 + i r/2`. -/
noncomputable def zq (r : ℝ) : ℂ := (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I

theorem zq_re (r : ℝ) : (zq r).re = 1 / 4 := by simp [zq]

theorem zq_eq (r : ℝ) : zq r = ⟨1 / 4, r / 2⟩ := by
  apply Complex.ext <;> simp [zq]

theorem zq_not_pole (r : ℝ) (m : ℕ) : zq r ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  rw [zq_re] at this
  simp at this
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- `r ↦ h(r) ψ(z_r)` is integrable, from Gauss's integral and the joint integrability
already in tree. -/
theorem integrable_hline_mul_digamma {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun r : ℝ => hline g r * Complex.digamma (zq r)) := by
  have hInt := integrable_prod hg
  have hinner : Integrable (fun r : ℝ =>
      ∫ t : ℝ in Ioi 0, hline g r * K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t) :=
    hInt.integral_prod_left
  have e : ∀ r : ℝ, hline g r * Complex.digamma (zq r) =
      -(Real.eulerMascheroniConstant : ℂ) * hline g r +
        ∫ t : ℝ in Ioi 0, hline g r * K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t := by
    intro r
    have hz : 0 < (zq r).re := by rw [zq_re]; norm_num
    rw [GppDigammaIntegral.digamma_eq_integral hz, integral_const_mul]
    simp only [K, zq]
    ring
  have : Integrable (fun r : ℝ => -(Real.eulerMascheroniConstant : ℂ) * hline g r +
      ∫ t : ℝ in Ioi 0, hline g r * K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t) :=
    ((hline_integrable hg).const_mul _).add hinner
  exact this.congr (Filter.Eventually.of_forall fun r => (e r).symm)

/-- For real `g`, `ĝ(1 - s) = conj ĝ(s̄)`; on the critical line, `ĝ(1/2 - i r) = conj ĝ(1/2 + i r)`. -/
theorem spectralTransform_one_sub (g : ℝ → ℝ) (r : ℝ) :
    spectralTransform g (1 - ((1 / 2 : ℂ) + r * Complex.I)) =
      (starRingEnd ℂ) (spectralTransform g ((1 / 2 : ℂ) + r * Complex.I)) := by
  unfold spectralTransform
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have e : (1 - ((1 / 2 : ℂ) + r * Complex.I) - 1 / 2) * u =
      (starRingEnd ℂ) (((1 / 2 : ℂ) + r * Complex.I - 1 / 2) * u) := by
    apply Complex.ext <;> simp
    norm_num
  rw [e]

/-- **The transform of an autocorrelation on the critical line is `|h|²`.** -/
theorem hline_autocorr {g : ℝ → ℝ} (hg : IsTestFunction g) (r : ℝ) :
    hline (autocorr g) r = ((‖hline g r‖ ^ 2 : ℝ) : ℂ) := by
  unfold hline
  rw [spectralTransform_autocorr hg, spectralTransform_one_sub, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- `w(r) = |h(r)|²` is integrable. -/
theorem integrable_sq {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun r : ℝ => ‖hline g r‖ ^ 2) := by
  have h := (hline_integrable (isTestFunction_autocorr hg)).re
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [hline_autocorr hg r, RCLike.re_to_complex, Complex.ofReal_re]

/-- `w · Re ψ(z_r)` is integrable. -/
theorem integrable_sq_mul_re {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 * (Complex.digamma (zq r)).re) := by
  have h := (integrable_hline_mul_digamma (isTestFunction_autocorr hg)).re
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [hline_autocorr hg r, RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- `∫ |h|² = 2π a(0)`. -/
theorem integral_sq {g : ℝ → ℝ} (hg : IsTestFunction g) :
    ∫ r : ℝ, ‖hline g r‖ ^ 2 = 2 * Real.pi * autocorr g 0 := by
  have h := integral_hline (isTestFunction_autocorr hg)
  have hre := congrArg Complex.re h
  have hir := integral_re (hline_integrable (isTestFunction_autocorr hg))
  simp only [RCLike.re_to_complex] at hir
  rw [← hir] at hre
  simp only [hline_autocorr hg, Complex.ofReal_re] at hre
  rw [hre]
  simp

/-- **Real-form identification for an autocorrelation.**
`archimedeanTerm a = (1/2π) ∫ |h(r)|² (Re ψ(z_r) - log π) dr`. -/
theorem archimedeanTerm_autocorr_eq {g : ℝ → ℝ} (hg : IsTestFunction g) :
    GppArchimedeanFloor.archimedeanTerm (autocorr g) =
      (1 / (2 * Real.pi)) *
        ∫ r : ℝ, ‖hline g r‖ ^ 2 * ((Complex.digamma (zq r)).re - Real.log Real.pi) := by
  have hid := archimedean_identification (isTestFunction_autocorr hg)
  have hre := congrArg Complex.re hid
  rw [Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  have hint := integrable_hline_mul_digamma (isTestFunction_autocorr hg)
  have hzq : (fun r : ℝ => hline (autocorr g) r *
      Complex.digamma ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I)) =
      fun r => hline (autocorr g) r * Complex.digamma (zq r) := rfl
  have hir := integral_re hint
  simp only [RCLike.re_to_complex] at hir
  rw [hzq, ← hir] at hre
  simp only [hline_autocorr hg, Complex.re_ofReal_mul] at hre
  -- hre : (1/2π) * ∫ w Re ψ = archimedeanTerm a + a 0 * log π
  have hsplit : ∫ r : ℝ, ‖hline g r‖ ^ 2 * ((Complex.digamma (zq r)).re - Real.log Real.pi) =
      (∫ r : ℝ, ‖hline g r‖ ^ 2 * (Complex.digamma (zq r)).re) -
        Real.log Real.pi * ∫ r : ℝ, ‖hline g r‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_sub (integrable_sq_mul_re hg)
      ((integrable_sq hg).const_mul _)]
    congr 1; funext r; ring
  rw [hsplit, integral_sq hg, mul_sub, hre]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The constant the certificate puts on `|r| ≥ T`: `c_T = log(T/(2π)) - 1/T`. -/
noncomputable def cT (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi)) - 1 / T

/-- The floor on both half-lines: for `|r| ≥ 2`, `Re ψ(z_r) - log π ≥ log(|r|/(2π)) - 1/|r|`. -/
theorem re_digamma_zq_ge {r : ℝ} (hr : 2 ≤ |r|) :
    Real.log (|r| / (2 * Real.pi)) - 1 / |r| ≤ (Complex.digamma (zq r)).re - Real.log Real.pi := by
  have hfloor := GppDigammaVerticalFloor.re_digamma_quarter_ge |r| hr
  have hsym : (Complex.digamma (zq r)).re = (Complex.digamma ⟨1 / 4, |r| / 2⟩).re := by
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h, zq_eq]
    · rw [abs_of_nonpos h]
      have hc : zq r = (starRingEnd ℂ) ⟨1 / 4, -r / 2⟩ := by
        apply Complex.ext <;> simp [zq]
        ring
      have hnp : ∀ m : ℕ, (⟨1 / 4, -r / 2⟩ : ℂ) ≠ -m := by
        intro m hm
        have := congrArg Complex.re hm
        simp at this
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [hc, GppDigammaQuarterSech.digamma_conj hnp, Complex.conj_re]
  rw [hsym]
  exact hfloor

/-- On `|r| ≥ T ≥ 2` the shifted symbol `Re ψ(z_r) - log π - c_T` is nonnegative. -/
theorem shifted_symbol_nonneg {T r : ℝ} (hT : 2 ≤ T) (hr : T ≤ |r|) :
    0 ≤ (Complex.digamma (zq r)).re - Real.log Real.pi - cT T := by
  have hT0 : 0 < T := by linarith
  have h := re_digamma_zq_ge (le_trans hT hr)
  have hmono_log : Real.log (T / (2 * Real.pi)) ≤ Real.log (|r| / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hr (by positivity))
  have hmono_inv : 1 / |r| ≤ 1 / T := one_div_le_one_div_of_le hT0 hr
  unfold cT
  linarith

/-- **Frequency split of the archimedean term.** For a real test function `g` and `T ≥ 2`,

  `c_T · a(0) + (1/2π) ∫_{-T}^{T} |h|² (Re ψ(z_r) - log π - c_T) dr ≤ archimedeanTerm a`. -/
theorem archimedeanTerm_autocorr_ge {g : ℝ → ℝ} (hg : IsTestFunction g) {T : ℝ} (hT : 2 ≤ T) :
    cT T * autocorr g 0 + (1 / (2 * Real.pi)) *
        ∫ r in Ioo (-T) T, ‖hline g r‖ ^ 2 * ((Complex.digamma (zq r)).re - Real.log Real.pi - cT T)
      ≤ GppArchimedeanFloor.archimedeanTerm (autocorr g) := by
  set F : ℝ → ℝ := fun r => ‖hline g r‖ ^ 2 *
    ((Complex.digamma (zq r)).re - Real.log Real.pi - cT T) with hF
  have hFint : Integrable F := by
    have h1 := integrable_sq_mul_re hg
    have h2 := (integrable_sq hg).mul_const (Real.log Real.pi + cT T)
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hF, Pi.sub_apply]; ring
  -- the full integral of F
  have hfull : ∫ r : ℝ, F r =
      2 * Real.pi * GppArchimedeanFloor.archimedeanTerm (autocorr g)
        - cT T * (2 * Real.pi * autocorr g 0) := by
    have heq := archimedeanTerm_autocorr_eq hg
    have hs : ∫ r : ℝ, F r = (∫ r : ℝ, ‖hline g r‖ ^ 2 *
        ((Complex.digamma (zq r)).re - Real.log Real.pi)) - cT T * ∫ r : ℝ, ‖hline g r‖ ^ 2 := by
      rw [← integral_const_mul, ← integral_sub _ ((integrable_sq hg).const_mul _)]
      · congr 1; funext r; simp only [hF]; ring
      · have h1 := integrable_sq_mul_re hg
        have h2 := (integrable_sq hg).mul_const (Real.log Real.pi)
        refine (h1.sub h2).congr (Filter.Eventually.of_forall fun r => ?_)
        simp only [Pi.sub_apply]; ring
    rw [hs, integral_sq hg, heq]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  -- dropping |r| ≥ T only lowers the integral
  have hcompl : ∀ r ∈ (Ioo (-T) T)ᶜ, 0 ≤ F r := by
    intro r hr
    have hr' : T ≤ |r| := by
      simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hr
      rcases hr with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; exact h
    exact mul_nonneg (sq_nonneg _) (shifted_symbol_nonneg hT hr')
  have hdrop : ∫ r in Ioo (-T) T, F r ≤ ∫ r : ℝ, F r := by
    have hsplit := integral_add_compl (measurableSet_Ioo (a := -T) (b := T)) hFint
    have hnn : 0 ≤ ∫ r in (Ioo (-T) T)ᶜ, F r := by
      refine setIntegral_nonneg measurableSet_Ioo.compl ?_
      intro r hr
      exact hcompl r hr
    linarith
  rw [hfull] at hdrop
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hdrop h2pi.le
  have e : 1 / (2 * Real.pi) * (2 * Real.pi * GppArchimedeanFloor.archimedeanTerm (autocorr g)
      - cT T * (2 * Real.pi * autocorr g 0)) =
      GppArchimedeanFloor.archimedeanTerm (autocorr g) - cT T * autocorr g 0 := by
    field_simp
  rw [e] at this
  show cT T * autocorr g 0 + 1 / (2 * Real.pi) * ∫ r in Ioo (-T) T, F r ≤ _
  linarith

end GppArchimedeanFrequencySplit
