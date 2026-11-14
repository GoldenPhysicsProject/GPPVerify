import GppVerify.RiemannHypothesis.ArchimedeanFrequencySplit
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity

/-!
# The rung-1 one-stroke reduction `Q(f) ≥ R(f)`

Let `g` be a real test function, `a = autocorr g` and `h(r) = ĝ(1/2 + i r)`. Suppose `a`
vanishes outside `[-L, L]` with `L < log 4`. Then only `n = 2, 3` enter the prime side, and
for every `T ≥ 2`

  `weilForm a ≥ poleTerm a + β(T) · a(0) + (1/2π) ∫_{-T}^{T} |h(r)|² (Ψ(r) - β(T)) dr`,

(`weilForm_autocorr_ge`). Here
* `Ψ(r) = Re ψ(1/4 + i r/2) - log π - Σ_{n∈{2,3}} 2Λ(n)/√n cos(r log n)` is
  `GppDigammaVerticalFloor.rungOneSymbol`;
* `β(T) = log(T/(2π)) - 1/T - A`, with `A = 2 log 2/√2 + 2 log 3/√3`, is `rungOneBeta`.

This is the one-stroke frequency-split reduction of Zhu (arXiv:2608.24827, Thm 1.1) at rung 1.
Grok's Arb certificate (`GPPDiscovery5/s27`) bounds the right-hand side from below at `T = 100`,
`L = 11/10` (supp `f ⊂ [-11/20, 11/20]`). In this lane the reduction itself was the open
analytic step; what remains is the certificate for the right-hand side (quadrature error and
the positive-definiteness check).

Supporting results:
* `autocorr_eq_integral_cos`: `a(v) = (1/2π) ∫ |h(r)|² cos(r v) dr`.
* `primeSide_autocorr_eq`: `primeSide a = (1/2π) ∫ |h(r)|² P(r) dr`, with `P` the `n = 2, 3`
  cosine sum.

Unconditional. No `sorry`, no axioms, no named premises. Nothing here concerns the zeros.
-/

namespace GppRungOneReduction

open Complex Set MeasureTheory ArithmeticFunction GppMeyerSpectralWeil GppArchimedeanId
  GppAutocorrTransport GppArithmeticReflection GppArchimedeanFrequencySplit
  GppDigammaVerticalFloor GppWeilLadder

/-- `|h(r)|² cos(r v)` is integrable. -/
theorem integrable_sq_mul_cos {g : ℝ → ℝ} (hg : IsTestFunction g) (v : ℝ) :
    Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 * Real.cos (r * v)) := by
  have h := (integrable_exp_mul_hline (isTestFunction_autocorr hg) v).re
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [hline_autocorr hg r, RCLike.re_to_complex]
  have e : -(Complex.I * (r : ℂ) * (v : ℂ)) = ((-(r * v) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- **Inversion for the autocorrelation:** `a(v) = (1/2π) ∫ |h(r)|² cos(r v) dr`. -/
theorem autocorr_eq_integral_cos {g : ℝ → ℝ} (hg : IsTestFunction g) (v : ℝ) :
    autocorr g v = (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖hline g r‖ ^ 2 * Real.cos (r * v) := by
  have h := inversion (isTestFunction_autocorr hg) v
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre
  have hir := integral_re (integrable_exp_mul_hline (isTestFunction_autocorr hg) v)
  simp only [RCLike.re_to_complex] at hir
  rw [← hir] at hre
  rw [hre]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [hline_autocorr hg r]
  have e : -(Complex.I * (r : ℂ) * (v : ℂ)) = ((-(r * v) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- The `n = 2, 3` truncation of the prime side. -/
theorem primeSide_eq_two_three {f : ℝ → ℝ} {L : ℝ} (hf : HasSupportIn f L)
    (hL : L < Real.log 4) :
    primeSide f = (Real.log 2 / Real.sqrt 2) * (f (Real.log 2) + f (-(Real.log 2)))
      + (Real.log 3 / Real.sqrt 3) * (f (Real.log 3) + f (-(Real.log 3))) := by
  have h4 : L < Real.log ((3 : ℕ) + 1) := by norm_num; exact hL
  rw [primeSide_eq_truncation hf h4]
  have hnot : ¬ IsPrimePow 1 := not_isPrimePow_one
  simp [Finset.sum_range_succ, vonMangoldt_apply_one,
    vonMangoldt_apply_prime Nat.prime_two, vonMangoldt_apply_prime Nat.prime_three]

/-- **The prime side in frequency form** at rung 1. -/
theorem primeSide_autocorr_eq {g : ℝ → ℝ} (hg : IsTestFunction g) {L : ℝ}
    (hsupp : HasSupportIn (autocorr g) L) (hL : L < Real.log 4) :
    primeSide (autocorr g) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖hline g r‖ ^ 2 * rungOnePrimeCos r := by
  rw [primeSide_eq_two_three hsupp hL]
  simp only [autocorr_eq_integral_cos hg]
  have hc : ∀ v : ℝ, (fun r : ℝ => ‖hline g r‖ ^ 2 * Real.cos (r * -v)) =
      fun r => ‖hline g r‖ ^ 2 * Real.cos (r * v) := by
    intro v; funext r; rw [mul_neg, Real.cos_neg]
  rw [hc, hc]
  have i2 := integrable_sq_mul_cos hg (Real.log 2)
  have i3 := integrable_sq_mul_cos hg (Real.log 3)
  have hsum : ∫ r : ℝ, ‖hline g r‖ ^ 2 * rungOnePrimeCos r =
      (2 * Real.log 2 / Real.sqrt 2) * (∫ r : ℝ, ‖hline g r‖ ^ 2 * Real.cos (r * Real.log 2))
        + (2 * Real.log 3 / Real.sqrt 3) *
          (∫ r : ℝ, ‖hline g r‖ ^ 2 * Real.cos (r * Real.log 3)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i2.const_mul _)
      (i3.const_mul _)]
    congr 1; funext r; unfold rungOnePrimeCos; ring
  rw [hsum]
  ring

/-- `|h|² · P` is integrable. -/
theorem integrable_sq_mul_primeCos {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 * rungOnePrimeCos r) := by
  have i2 := (integrable_sq_mul_cos hg (Real.log 2)).const_mul (2 * Real.log 2 / Real.sqrt 2)
  have i3 := (integrable_sq_mul_cos hg (Real.log 3)).const_mul (2 * Real.log 3 / Real.sqrt 3)
  refine (i2.add i3).congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply]; unfold rungOnePrimeCos; ring

/-- `Ψ(r) - β(T) ≥ 0` for `|r| ≥ T ≥ 2`, on both half-lines. -/
theorem symbol_sub_beta_nonneg {T r : ℝ} (hT : 2 ≤ T) (hr : T ≤ |r|) :
    0 ≤ rungOneSymbol r - rungOneBeta T := by
  have h1 := shifted_symbol_nonneg hT hr
  have h2 := rungOnePrimeCos_le r
  have hz : (Complex.digamma (zq r)).re = (Complex.digamma ⟨1 / 4, r / 2⟩).re := by
    rw [zq_eq]
  unfold rungOneSymbol rungOneBeta
  unfold cT at h1
  rw [hz] at h1
  linarith

/-- **The rung-1 one-stroke reduction.** For a real test function `g` whose autocorrelation
vanishes outside `[-L, L]`, `L < log 4`, and every `T ≥ 2`,

  `poleTerm a + β(T) a(0) + (1/2π) ∫_{-T}^{T} |h|² (Ψ - β(T)) ≤ weilForm a`. -/
theorem weilForm_autocorr_ge {g : ℝ → ℝ} (hg : IsTestFunction g) {L : ℝ}
    (hsupp : HasSupportIn (autocorr g) L) (hL : L < Real.log 4) {T : ℝ} (hT : 2 ≤ T) :
    poleTerm (autocorr g) + rungOneBeta T * autocorr g 0 +
        (1 / (2 * Real.pi)) * ∫ r in Ioo (-T) T,
          ‖hline g r‖ ^ 2 * (rungOneSymbol r - rungOneBeta T)
      ≤ weilForm (autocorr g) := by
  set F : ℝ → ℝ := fun r => ‖hline g r‖ ^ 2 * (rungOneSymbol r - rungOneBeta T) with hF
  have hsym : ∀ r, rungOneSymbol r =
      ((Complex.digamma (zq r)).re - Real.log Real.pi) - rungOnePrimeCos r := by
    intro r; unfold rungOneSymbol; rw [zq_eq]
  -- integrability of F
  have hA : Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 *
      ((Complex.digamma (zq r)).re - Real.log Real.pi)) := by
    refine ((integrable_sq_mul_re hg).sub ((integrable_sq hg).mul_const (Real.log Real.pi))).congr
      (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply]; ring
  have hFint : Integrable F := by
    refine ((hA.sub (integrable_sq_mul_primeCos hg)).sub
      ((integrable_sq hg).mul_const (rungOneBeta T))).congr
      (Filter.Eventually.of_forall fun r => ?_)
    simp only [hF, Pi.sub_apply, hsym]; ring
  -- the full integral of F
  have hfull : ∫ r : ℝ, F r =
      2 * Real.pi * (weilForm (autocorr g) - poleTerm (autocorr g))
        - rungOneBeta T * (2 * Real.pi * autocorr g 0) := by
    have heq := archimedeanTerm_autocorr_eq hg
    have hp := primeSide_autocorr_eq hg hsupp hL
    have hs : ∫ r : ℝ, F r =
        (∫ r : ℝ, ‖hline g r‖ ^ 2 * ((Complex.digamma (zq r)).re - Real.log Real.pi))
          - (∫ r : ℝ, ‖hline g r‖ ^ 2 * rungOnePrimeCos r)
          - rungOneBeta T * ∫ r : ℝ, ‖hline g r‖ ^ 2 := by
      have hAP : Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 *
          ((Complex.digamma (zq r)).re - Real.log Real.pi) - ‖hline g r‖ ^ 2 * rungOnePrimeCos r) :=
        hA.sub (integrable_sq_mul_primeCos hg)
      have hB : Integrable (fun r : ℝ => rungOneBeta T * ‖hline g r‖ ^ 2) :=
        (integrable_sq hg).const_mul _
      have e1 : ∫ r : ℝ, F r = ∫ r : ℝ, ((‖hline g r‖ ^ 2 *
          ((Complex.digamma (zq r)).re - Real.log Real.pi) - ‖hline g r‖ ^ 2 * rungOnePrimeCos r)
          - rungOneBeta T * ‖hline g r‖ ^ 2) := by
        congr 1; funext r; simp only [hF, hsym]; ring
      rw [e1, integral_sub hAP hB, integral_sub hA (integrable_sq_mul_primeCos hg),
        integral_const_mul]
    rw [hs, integral_sq hg]
    unfold weilForm
    rw [heq, hp]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hcompl : ∀ r ∈ (Ioo (-T) T)ᶜ, 0 ≤ F r := by
    intro r hr
    have hr' : T ≤ |r| := by
      simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hr
      rcases hr with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; exact h
    exact mul_nonneg (sq_nonneg _) (symbol_sub_beta_nonneg hT hr')
  have hdrop : ∫ r in Ioo (-T) T, F r ≤ ∫ r : ℝ, F r := by
    have hsplit := integral_add_compl (measurableSet_Ioo (a := -T) (b := T)) hFint
    have hnn : 0 ≤ ∫ r in (Ioo (-T) T)ᶜ, F r :=
      setIntegral_nonneg measurableSet_Ioo.compl hcompl
    linarith
  rw [hfull] at hdrop
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hdrop h2pi.le
  have e : 1 / (2 * Real.pi) * (2 * Real.pi * (weilForm (autocorr g) - poleTerm (autocorr g))
      - rungOneBeta T * (2 * Real.pi * autocorr g 0)) =
      weilForm (autocorr g) - poleTerm (autocorr g) - rungOneBeta T * autocorr g 0 := by
    field_simp
  rw [e] at this
  show poleTerm (autocorr g) + rungOneBeta T * autocorr g 0 +
    1 / (2 * Real.pi) * ∫ r in Ioo (-T) T, F r ≤ _
  linarith

end GppRungOneReduction
