import GppVerify.RiemannHypothesis.RungOneReduction

/-!
# The one-stroke reduction below `log 3`: only the prime `2`

The variant of `GppRungOneReduction.weilForm_autocorr_ge` for windows whose autocorrelation vanishes
outside `[-L, L]` with `L < log 3`. Then only `n = 2` enters the prime side, so the prime cosine sum
is `A₂ cos(r log 2)` with `A₂ = 2 log 2/√2 ≈ 0.980` instead of `A ≈ 2.249`, and

  `weilForm a ≥ poleTerm a + β₂(T) a(0) + (1/2π) ∫_{-T}^{T} |h(r)|² (Ψ₂(r) - β₂(T)) dr`

for every `T ≥ 2`, with `Ψ₂(r) = Re ψ(1/4 + i r/2) - log π - A₂ cos(r log 2)` and
`β₂(T) = log(T/(2π)) - 1/T - A₂` (`weilForm_autocorr_ge_two`).

Why it matters for a certificate: `β₂(T) > 0` already at `T ≈ 17` (versus `T ≈ 60` for `β`), and the
size of every matrix entry of a Gram certificate is governed by `T ℓ`. At the first window where the
prime `2` is visible (`supp f ⊂ [-0.36, 0.36]`, so `L = 0.72`), float experiments
(GPP-bridge `work/claude-code/rung1/lean_form_scan_p2.py`) give `λ_min ≈ 3.5e-4` (even) and
`2.4e-2` (odd) at `T = 25`, converged at eight Legendre modes per parity. That is evidence for a
target, not a bound.

Unconditional. No `sorry`, no axioms, no named premises. Nothing here concerns the zeros.
-/

namespace GppRungOneReductionTwo

open Complex Set MeasureTheory ArithmeticFunction GppMeyerSpectralWeil GppArchimedeanId
  GppAutocorrTransport GppArithmeticReflection GppArchimedeanFrequencySplit
  GppDigammaVerticalFloor GppWeilLadder GppRungOneReduction

/-- `A₂ = 2 log 2/√2`, the triangle bound for the `n = 2` cosine. -/
noncomputable def primeTwoA : ℝ := 2 * Real.log 2 / Real.sqrt 2

/-- The `n = 2` cosine `A₂ cos(r log 2)`. -/
noncomputable def primeTwoCos (r : ℝ) : ℝ := primeTwoA * Real.cos (r * Real.log 2)

/-- `Ψ₂(r) = Re ψ(1/4 + i r/2) - log π - A₂ cos(r log 2)`. -/
noncomputable def symbolTwo (r : ℝ) : ℝ :=
  (Complex.digamma ⟨1 / 4, r / 2⟩).re - Real.log Real.pi - primeTwoCos r

/-- `β₂(T) = log(T/(2π)) - 1/T - A₂`. -/
noncomputable def betaTwo (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi)) - 1 / T - primeTwoA

theorem primeTwoA_nonneg : 0 ≤ primeTwoA := by
  unfold primeTwoA
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity

theorem primeTwoCos_le (r : ℝ) : primeTwoCos r ≤ primeTwoA := by
  unfold primeTwoCos
  have := mul_le_mul_of_nonneg_left (Real.cos_le_one (r * Real.log 2)) primeTwoA_nonneg
  linarith

/-- The `n = 2` truncation of the prime side, for support inside `(-log 3, log 3)`. -/
theorem primeSide_eq_two {f : ℝ → ℝ} {L : ℝ} (hf : HasSupportIn f L) (hL : L < Real.log 3) :
    primeSide f = (Real.log 2 / Real.sqrt 2) * (f (Real.log 2) + f (-(Real.log 2))) := by
  have h3 : L < Real.log ((2 : ℕ) + 1) := by norm_num; exact hL
  rw [primeSide_eq_truncation hf h3]
  have hnot : ¬ IsPrimePow 1 := not_isPrimePow_one
  simp [Finset.sum_range_succ, vonMangoldt_apply_one, vonMangoldt_apply_prime Nat.prime_two]

/-- **The prime side in frequency form** below `log 3`. -/
theorem primeSide_autocorr_eq_two {g : ℝ → ℝ} (hg : IsTestFunction g) {L : ℝ}
    (hsupp : HasSupportIn (autocorr g) L) (hL : L < Real.log 3) :
    primeSide (autocorr g) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖hline g r‖ ^ 2 * primeTwoCos r := by
  rw [primeSide_eq_two hsupp hL]
  simp only [autocorr_eq_integral_cos hg]
  have hc : (fun r : ℝ => ‖hline g r‖ ^ 2 * Real.cos (r * -Real.log 2)) =
      fun r => ‖hline g r‖ ^ 2 * Real.cos (r * Real.log 2) := by
    funext r; rw [mul_neg, Real.cos_neg]
  rw [hc]
  have hsum : ∫ r : ℝ, ‖hline g r‖ ^ 2 * primeTwoCos r =
      primeTwoA * ∫ r : ℝ, ‖hline g r‖ ^ 2 * Real.cos (r * Real.log 2) := by
    rw [← integral_const_mul]
    congr 1; funext r; unfold primeTwoCos; ring
  rw [hsum]
  unfold primeTwoA
  ring

theorem integrable_sq_mul_primeTwoCos {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 * primeTwoCos r) := by
  refine ((integrable_sq_mul_cos hg (Real.log 2)).const_mul primeTwoA).congr
    (Filter.Eventually.of_forall fun r => ?_)
  simp only; unfold primeTwoCos; ring

/-- `Ψ₂(r) - β₂(T) ≥ 0` for `|r| ≥ T ≥ 2`. -/
theorem symbolTwo_sub_betaTwo_nonneg {T r : ℝ} (hT : 2 ≤ T) (hr : T ≤ |r|) :
    0 ≤ symbolTwo r - betaTwo T := by
  have h1 := shifted_symbol_nonneg hT hr
  have h2 := primeTwoCos_le r
  have hz : (Complex.digamma (zq r)).re = (Complex.digamma ⟨1 / 4, r / 2⟩).re := by
    rw [zq_eq]
  unfold symbolTwo betaTwo
  unfold cT at h1
  rw [hz] at h1
  linarith

/-- **The one-stroke reduction below `log 3`.** For a real test function `g` whose autocorrelation
vanishes outside `[-L, L]`, `L < log 3`, and every `T ≥ 2`,

  `poleTerm a + β₂(T) a(0) + (1/2π) ∫_{-T}^{T} |h|² (Ψ₂ - β₂(T)) ≤ weilForm a`. -/
theorem weilForm_autocorr_ge_two {g : ℝ → ℝ} (hg : IsTestFunction g) {L : ℝ}
    (hsupp : HasSupportIn (autocorr g) L) (hL : L < Real.log 3) {T : ℝ} (hT : 2 ≤ T) :
    poleTerm (autocorr g) + betaTwo T * autocorr g 0 +
        (1 / (2 * Real.pi)) * ∫ r in Ioo (-T) T, ‖hline g r‖ ^ 2 * (symbolTwo r - betaTwo T)
      ≤ weilForm (autocorr g) := by
  set F : ℝ → ℝ := fun r => ‖hline g r‖ ^ 2 * (symbolTwo r - betaTwo T) with hF
  have hsym : ∀ r, symbolTwo r =
      ((Complex.digamma (zq r)).re - Real.log Real.pi) - primeTwoCos r := by
    intro r; unfold symbolTwo; rw [zq_eq]
  have hA : Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 *
      ((Complex.digamma (zq r)).re - Real.log Real.pi)) := by
    refine ((integrable_sq_mul_re hg).sub ((integrable_sq hg).mul_const (Real.log Real.pi))).congr
      (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply]; ring
  have hFint : Integrable F := by
    refine ((hA.sub (integrable_sq_mul_primeTwoCos hg)).sub
      ((integrable_sq hg).mul_const (betaTwo T))).congr
      (Filter.Eventually.of_forall fun r => ?_)
    simp only [hF, Pi.sub_apply, hsym]; ring
  have hfull : ∫ r : ℝ, F r =
      2 * Real.pi * (weilForm (autocorr g) - poleTerm (autocorr g))
        - betaTwo T * (2 * Real.pi * autocorr g 0) := by
    have heq := archimedeanTerm_autocorr_eq hg
    have hp := primeSide_autocorr_eq_two hg hsupp hL
    have hs : ∫ r : ℝ, F r =
        (∫ r : ℝ, ‖hline g r‖ ^ 2 * ((Complex.digamma (zq r)).re - Real.log Real.pi))
          - (∫ r : ℝ, ‖hline g r‖ ^ 2 * primeTwoCos r)
          - betaTwo T * ∫ r : ℝ, ‖hline g r‖ ^ 2 := by
      have hAP : Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 *
          ((Complex.digamma (zq r)).re - Real.log Real.pi) - ‖hline g r‖ ^ 2 * primeTwoCos r) :=
        hA.sub (integrable_sq_mul_primeTwoCos hg)
      have hB : Integrable (fun r : ℝ => betaTwo T * ‖hline g r‖ ^ 2) :=
        (integrable_sq hg).const_mul _
      have e1 : ∫ r : ℝ, F r = ∫ r : ℝ, ((‖hline g r‖ ^ 2 *
          ((Complex.digamma (zq r)).re - Real.log Real.pi) - ‖hline g r‖ ^ 2 * primeTwoCos r)
          - betaTwo T * ‖hline g r‖ ^ 2) := by
        congr 1; funext r; simp only [hF, hsym]; ring
      rw [e1, integral_sub hAP hB, integral_sub hA (integrable_sq_mul_primeTwoCos hg),
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
    exact mul_nonneg (sq_nonneg _) (symbolTwo_sub_betaTwo_nonneg hT hr')
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
      - betaTwo T * (2 * Real.pi * autocorr g 0)) =
      weilForm (autocorr g) - poleTerm (autocorr g) - betaTwo T * autocorr g 0 := by
    field_simp
  rw [e] at this
  show poleTerm (autocorr g) + betaTwo T * autocorr g 0 +
    1 / (2 * Real.pi) * ∫ r in Ioo (-T) T, F r ≤ _
  linarith

end GppRungOneReductionTwo

#print axioms GppRungOneReductionTwo.weilForm_autocorr_ge_two
