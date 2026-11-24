import GppVerify.RiemannHypothesis.RungOneReductionTwo

/-!
# The window form as a bilinear form: pole factorisation and the minorant form

Toward a certificate for `weilForm (autocorr g) ≥ 0` on a window `supp g ⊂ [-ℓ, ℓ]`.

* `poleTerm_autocorr_eq`: the pole term of an autocorrelation factorises,
  `poleTerm (autocorr g) = 2 G₊(g) G₋(g)` with `G_±(g) = ∫ g(u) e^{±u/2} du`. (From the in-tree
  convolution identity `spectralTransform_autocorr` at `s = 1`, `s = 0`.) So the pole term is a
  rank-two quadratic form, `+` on even and `-` on odd functions.
* `minorantForm`: for a symbol minorant `m ≤ Ψ₂ - β₂(T)` on `(-T, T)`, the form
  `2 G₊ G₋ + β₂(T) ∫ g² + (1/2π) ∫_{-T}^{T} |h|² m`, and `minorantForm_le_weilForm`: it is a lower
  bound for `weilForm (autocorr g)` when `L < log 3`.

Unconditional. No `sorry`, no axioms, no named premises.
-/

namespace GppWindowGramForm

open Complex Set MeasureTheory GppMeyerSpectralWeil GppArchimedeanId GppAutocorrTransport
  GppArithmeticReflection GppArchimedeanFrequencySplit GppWeilLadder GppRungOneReduction
  GppRungOneReductionTwo

/-- `∫ f(u) e^{c u} du`, the real Laplace transform at a real point. -/
noncomputable def realLaplace (f : ℝ → ℝ) (c : ℝ) : ℝ := ∫ u, f u * Real.exp (c * u)

theorem integrable_mul_exp {f : ℝ → ℝ} (hf : IsTestFunction f) (c : ℝ) :
    Integrable (fun u => f u * Real.exp (c * u)) :=
  (hf.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport (hf.2.mul_right)

/-- On the real axis the spectral transform is the real Laplace transform. -/
theorem spectralTransform_real (f : ℝ → ℝ) (c : ℝ) :
    spectralTransform f ((c : ℂ) + 1 / 2) = (realLaplace f c : ℂ) := by
  unfold spectralTransform realLaplace
  rw [← integral_complex_ofReal]
  congr 1; funext u
  push_cast
  ring_nf

/-- **The pole term of an autocorrelation factorises:** `poleTerm (autocorr g) = 2 G₊ G₋`. -/
theorem poleTerm_autocorr_eq {g : ℝ → ℝ} (hg : IsTestFunction g) :
    poleTerm (autocorr g) = 2 * realLaplace g (1 / 2) * realLaplace g (-1 / 2) := by
  have ha := isTestFunction_autocorr hg
  have h1 : spectralTransform (autocorr g) (((1 / 2 : ℝ) : ℂ) + 1 / 2) =
      spectralTransform g (((1 / 2 : ℝ) : ℂ) + 1 / 2) *
        spectralTransform g (((-1 / 2 : ℝ) : ℂ) + 1 / 2) := by
    have := spectralTransform_autocorr hg (((1 / 2 : ℝ) : ℂ) + 1 / 2)
    rw [this]; congr 2; push_cast; ring
  have h0 : spectralTransform (autocorr g) (((-1 / 2 : ℝ) : ℂ) + 1 / 2) =
      spectralTransform g (((-1 / 2 : ℝ) : ℂ) + 1 / 2) *
        spectralTransform g (((1 / 2 : ℝ) : ℂ) + 1 / 2) := by
    have := spectralTransform_autocorr hg (((-1 / 2 : ℝ) : ℂ) + 1 / 2)
    rw [this]; congr 2; push_cast; ring
  simp only [spectralTransform_real] at h1 h0
  have r1 : realLaplace (autocorr g) (1 / 2) = realLaplace g (1 / 2) * realLaplace g (-1 / 2) := by
    exact_mod_cast h1
  have r0 : realLaplace (autocorr g) (-1 / 2) = realLaplace g (-1 / 2) * realLaplace g (1 / 2) := by
    exact_mod_cast h0
  have hsplit : poleTerm (autocorr g) =
      realLaplace (autocorr g) (1 / 2) + realLaplace (autocorr g) (-1 / 2) := by
    unfold poleTerm realLaplace
    rw [← integral_add (integrable_mul_exp ha _) (integrable_mul_exp ha _)]
    congr 1; funext u
    rw [Real.cosh_eq]
    ring_nf
  rw [hsplit, r1, r0]
  ring

/-- `|h|² (Ψ₂ - β₂(T))` is integrable on `ℝ`. -/
theorem integrable_sq_mul_symbolTwo_sub {g : ℝ → ℝ} (hg : IsTestFunction g) (T : ℝ) :
    Integrable (fun r : ℝ => ‖hline g r‖ ^ 2 * (symbolTwo r - betaTwo T)) := by
  have hA := (integrable_sq_mul_re hg).sub ((integrable_sq hg).mul_const (Real.log Real.pi))
  refine ((hA.sub (integrable_sq_mul_primeTwoCos hg)).sub
    ((integrable_sq hg).mul_const (betaTwo T))).congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Pi.sub_apply]
  unfold symbolTwo
  rw [← zq_eq]
  ring

/-- **The minorant form.** For a symbol minorant `m` on `[-T, T]`:
`2 G₊ G₋ + β₂(T) a(0) + (1/2π) ∫_{-T}^{T} |h|² m`. -/
noncomputable def minorantForm (m : ℝ → ℝ) (T : ℝ) (g : ℝ → ℝ) : ℝ :=
  2 * realLaplace g (1 / 2) * realLaplace g (-1 / 2) + betaTwo T * autocorr g 0 +
    (1 / (2 * Real.pi)) * ∫ r in Ioo (-T) T, ‖hline g r‖ ^ 2 * m r

/-- **The minorant form bounds the Weil form from below.** If `m ≤ Ψ₂ - β₂(T)` on `[-T, T]`, `m`
is integrable there, `T ≥ 2`, and `autocorr g` vanishes outside `[-L, L]` with `L < log 3`, then
`minorantForm m T g ≤ weilForm (autocorr g)`. -/
theorem minorantForm_le_weilForm {g : ℝ → ℝ} (hg : IsTestFunction g) {L : ℝ}
    (hsupp : HasSupportIn (autocorr g) L) (hL : L < Real.log 3) {T : ℝ} (hT : 2 ≤ T)
    {m : ℝ → ℝ} (hmi : IntegrableOn m (Icc (-T) T))
    (hm : ∀ r ∈ Icc (-T) T, m r ≤ symbolTwo r - betaTwo T) :
    minorantForm m T g ≤ weilForm (autocorr g) := by
  have hred := weilForm_autocorr_ge_two hg hsupp hL hT
  rw [poleTerm_autocorr_eq hg] at hred
  have hI1 : IntegrableOn (fun r => ‖hline g r‖ ^ 2 * m r) (Ioo (-T) T) := by
    have hc : ContinuousOn (fun r => ‖hline g r‖ ^ 2) (Icc (-T) T) :=
      ((hline_continuous hg).norm.pow 2).continuousOn
    exact (hmi.continuousOn_mul hc isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hI2 : IntegrableOn (fun r => ‖hline g r‖ ^ 2 * (symbolTwo r - betaTwo T)) (Ioo (-T) T) :=
    (integrable_sq_mul_symbolTwo_sub hg T).integrableOn
  have hmono : ∫ r in Ioo (-T) T, ‖hline g r‖ ^ 2 * m r ≤
      ∫ r in Ioo (-T) T, ‖hline g r‖ ^ 2 * (symbolTwo r - betaTwo T) :=
    setIntegral_mono_on hI1 hI2 measurableSet_Ioo fun r hr =>
      mul_le_mul_of_nonneg_left (hm r (Ioo_subset_Icc_self hr)) (sq_nonneg _)
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  unfold minorantForm
  nlinarith [mul_le_mul_of_nonneg_left hmono hpi]

end GppWindowGramForm

#print axioms GppWindowGramForm.poleTerm_autocorr_eq
#print axioms GppWindowGramForm.minorantForm_le_weilForm
