import GppVerify.RiemannHypothesis.WindowTail
import GppVerify.RiemannHypothesis.RungZeroPositivity

/-!
# The window theorem, conditional on the two finite inputs

Input (c) of the first-prime-visible-window certificate, and the assembly.

* `minorantForm_eq_B`: for a test function `g` vanishing outside `[-ℓ, ℓ]`, the minorant form of
  `GppWindowGramForm` is the window bilinear form `B(g, g)` of `GppWindowBilinear` with
  `β = β₂(T)`: every transform over `ℝ` is the transform over `[-ℓ, ℓ]`, `a(0) = ⟨g, g⟩`, and the
  `(-T, T)` set integral of `|h|² m` is the interval integral of `m Re(h conj h)`.
* `weilForm_autocorr_nonneg_of_window_certificate`: for `2ℓ < log 3` and `T ≥ 2`, if
  - (b) `m ≤ Ψ₂ - β₂(T)` on `[-T, T]` (`m` integrable, `|m| ≤ M`), and
  - (a) the finite block of `B` (with `β = β₂(T)`) on an orthogonal basis spanning `x^k`, `k < D`,
    satisfies `λ Σ d c² ≤ Σ c_j c_k B(φ_j, φ_k)`, together with the scalar tail condition of
    `GppWindowTail.window_form_nonneg`,

  then `weilForm (autocorr g) ≥ 0` for every test function `g` vanishing outside `[-ℓ, ℓ]`.

The hypotheses (a) and (b) are finite, checkable statements; neither is asserted here. This file
proves the implication only. Unconditional; no `sorry`, no axioms. Nothing here concerns the zeros.
-/

namespace GppWindowAssembly

open Complex Set MeasureTheory intervalIntegral GppMeyerSpectralWeil GppArchimedeanId
  GppArithmeticReflection GppWeilLadder GppRungOneReductionTwo GppWindowGramForm GppWindowBilinear
  GppWindowTail
open scoped ComplexConjugate

variable {ℓ : ℝ}

/-- A continuous function vanishing for `|x| > ℓ` also vanishes at `±ℓ`. -/
theorem eq_zero_of_le_abs {g : ℝ → ℝ} (hc : Continuous g) (hs : HasSupportIn g ℓ) {x : ℝ}
    (hx : ℓ ≤ |x|) : g x = 0 := by
  have hcl : IsClosed {y : ℝ | g y = 0} := isClosed_eq hc continuous_const
  have hsub : {y : ℝ | ℓ < |y|} ⊆ {y : ℝ | g y = 0} := fun y hy => hs y hy
  rcases hx.lt_or_eq with h | h
  · exact hs x h
  · -- |x| = ℓ: approach x from outside
    rcases le_total 0 x with h0 | h0
    · have hxl : x = ℓ := by rw [abs_of_nonneg h0] at h; exact h.symm
      have : Ioi ℓ ⊆ {y : ℝ | g y = 0} := fun y hy => hs y (by
        have : ℓ < y := hy
        have hl : 0 ≤ ℓ := h ▸ abs_nonneg x
        rw [abs_of_pos (by linarith)]; exact this)
      have hcl' := hcl.closure_subset_iff.mpr this
      rw [closure_Ioi] at hcl'
      exact hcl' (show x ∈ Ici ℓ from le_of_eq hxl.symm)
    · have hxl : x = -ℓ := by rw [abs_of_nonpos h0] at h; linarith
      have : Iio (-ℓ) ⊆ {y : ℝ | g y = 0} := fun y hy => hs y (by
        have : y < -ℓ := hy
        have hl : 0 ≤ ℓ := h ▸ abs_nonneg x
        rw [abs_of_neg (by linarith)]; linarith)
      have hcl' := hcl.closure_subset_iff.mpr this
      rw [closure_Iio] at hcl'
      exact hcl' (show x ∈ Iic (-ℓ) from le_of_eq hxl)

/-- For `f` vanishing off `[-ℓ, ℓ]`, the integral over `ℝ` is the interval integral. -/
theorem integral_eq_intervalIntegral {f : ℝ → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hℓ : 0 ≤ ℓ) (hf : ∀ x, ℓ ≤ |x| → f x = 0) :
    ∫ x, f x = ∫ x in (-ℓ)..ℓ, f x := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf x ?_).symm
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h.le

/-- **Input (c).** For a test function vanishing outside `[-ℓ, ℓ]`,
`minorantForm m T g = B ℓ T β₂(T) m g g`. -/
theorem minorantForm_eq_B {g : ℝ → ℝ} (hg : IsTestFunction g) (hℓ : 0 ≤ ℓ)
    (hs : HasSupportIn g ℓ) {T : ℝ} (hT : 0 ≤ T) (m : ℝ → ℝ) :
    minorantForm m T g = B ℓ T (betaTwo T) m g g := by
  have hz : ∀ x, ℓ ≤ |x| → g x = 0 := fun x hx => eq_zero_of_le_abs hg.1.continuous hs hx
  have hlap : ∀ c, realLaplace g c = lap ℓ g c := by
    intro c
    unfold realLaplace lap
    exact integral_eq_intervalIntegral hℓ fun x hx => by rw [hz x hx, zero_mul]
  have hip : GppArithmeticReflection.autocorr g 0 = ip ℓ g g := by
    rw [GppRungZeroPositivity.autocorr_zero_eq]
    unfold ip
    rw [integral_eq_intervalIntegral hℓ fun x hx => by rw [hz x hx]; ring]
    congr 1; funext x; ring
  have hh : ∀ r, hline g r = hw ℓ g r := by
    intro r
    unfold hline spectralTransform hw
    rw [integral_eq_intervalIntegral hℓ fun x hx => by rw [hz x hx]; simp]
    congr 1; funext x
    congr 2; push_cast; ring
  have hspec : ∫ r in Ioo (-T) T, ‖hline g r‖ ^ 2 * m r = spec ℓ T m g g := by
    unfold spec
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Ioc_eq_integral_Ioo]
    congr 1; funext r
    rw [hh, re_mul_conj_self]; ring
  unfold minorantForm B
  rw [hlap, hlap, hip, hspec]
  ring

/-- **The window theorem, conditional on its two finite inputs.** See the module docstring. -/
theorem weilForm_autocorr_nonneg_of_window_certificate {g : ℝ → ℝ} (hg : IsTestFunction g)
    (hℓ : 0 ≤ ℓ) (hs : HasSupportIn g ℓ) (hℓ3 : 2 * ℓ < Real.log 3) {T : ℝ} (hT : 2 ≤ T)
    {m : ℝ → ℝ} (hmi : IntegrableOn m (Icc (-T) T))
    (hm : ∀ r ∈ Icc (-T) T, m r ≤ symbolTwo r - betaTwo T)
    {Mm : ℝ} (hMm : ∀ r ∈ Icc (-T) T, |m r| ≤ Mm)
    {n D : ℕ} (φ : Fin n → ℝ → ℝ) (hφ : ∀ k, Continuous (φ k))
    (horth : ∀ j k, j ≠ k → ip ℓ (φ j) (φ k) = 0) (hd : ∀ k, 0 < ip ℓ (φ k) (φ k))
    (hspan : ∀ k < D, ∃ α : Fin n → ℝ, ∀ x, x ^ k = ∑ j, α j * φ j x)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hM : ∀ c : Fin n → ℝ, lam * ∑ k, ip ℓ (φ k) (φ k) * c k ^ 2 ≤
      ∑ j, ∑ k, c j * c k * B ℓ T (betaTwo T) m (φ j) (φ k))
    (hμ : 0 ≤ betaTwo T - 2 * ℓ * (2 * ((ℓ / 2) ^ D * Real.exp (ℓ / 2)) ^ 2 +
      Mm * T * ((T * ℓ) ^ D / D.factorial) ^ 2 / Real.pi))
    (hcond : (n : ℝ) * (2 * ℓ * (2 * Real.exp (ℓ / 2) * ((ℓ / 2) ^ D * Real.exp (ℓ / 2)) +
      Mm * T * ((T * ℓ) ^ D / D.factorial) / Real.pi)) ^ 2 ≤
      lam * (betaTwo T - 2 * ℓ * (2 * ((ℓ / 2) ^ D * Real.exp (ℓ / 2)) ^ 2 +
        Mm * T * ((T * ℓ) ^ D / D.factorial) ^ 2 / Real.pi))) :
    0 ≤ weilForm (GppArithmeticReflection.autocorr g) := by
  have hT0 : 0 ≤ T := by linarith
  have hsa : HasSupportIn (GppArithmeticReflection.autocorr g) (2 * ℓ) :=
    autocorr_hasSupportIn fun y hy => hs y (by linarith)
  have hle := minorantForm_le_weilForm hg hsa hℓ3 hT hmi hm
  have hmi' : IntervalIntegrable m volume (-T) T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hmi
  have hpos := window_form_nonneg hℓ hT0 hmi' hMm φ hφ horth hd hspan hlam hM hμ hcond
    hg.1.continuous
  rw [minorantForm_eq_B hg hℓ hs hT0] at hle
  linarith

end GppWindowAssembly

#print axioms GppWindowAssembly.minorantForm_eq_B
#print axioms GppWindowAssembly.weilForm_autocorr_nonneg_of_window_certificate
