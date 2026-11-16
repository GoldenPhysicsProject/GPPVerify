import GppVerify.RiemannHypothesis.BNNormOne

/-!
# The edge-overlap bound `|A_f(t)| ≤ ½ ‖f‖²` for `t > L/2`

For `f` supported in `[−L/2, L/2]` and a shift `t > L/2`, the supports of `f` and of its translate
`f(· − t)` overlap only in the edge interval `[t − L/2, L/2]`; there `f` and the translate sample *disjoint*
parts of `f`'s support (`[t − L/2, L/2]` and `[−L/2, L/2 − t]` are disjoint exactly when `t > L/2`), so
`|A_f(t)| = |∫ f(y) f(y − t)| ≤ ½(∫_S f² + ∫_{S − t} f²) ≤ ½ ‖f‖²`.

This is the disjoint-edge bound used in the first-prime-window index estimate (Turbo relay `7399083`,
step (1) of the filed formalisation order): at width `L = 18/25` the prime `2` has `log 2 > L/2`, so its
autocorrelation term is at most `‖f‖²/2`.

Elementary measure theory; no `sorry`, no axiom.
-/

open MeasureTheory Set
open GppArithmeticReflection
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

/-- **Edge-overlap bound.** `|f ⋆ f̃ (t)| ≤ ½ ‖f‖²` for `t > L/2` and `f` supported in `[−L/2, L/2]`. -/
theorem abs_autocorr_le_half {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {L : ℝ}
    (hs : ∀ y : ℝ, L / 2 < |y| → f y = 0) {t : ℝ} (ht : L / 2 < t) :
    |autocorr f t| ≤ autocorr f 0 / 2 := by
  have hsq := GppRungZeroPositivity.integrable_sq hf hc
  have hsh := GppRungZeroPositivity.integrable_sq_shift hf hc t
  set S : Set ℝ := Icc (t - L / 2) (L / 2) with hS
  set S' : Set ℝ := Icc (-(L / 2)) (L / 2 - t) with hS'
  have hSm : MeasurableSet S := measurableSet_Icc
  have hS'm : MeasurableSet S' := measurableSet_Icc
  have hdisj : Disjoint S' S := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [hS, hS', mem_Icc] at hx hx'
    linarith [hx.2, hx'.1]
  -- the product is supported on `S`
  have hsupp : ∀ y, y ∉ S → f y * f (y - t) = 0 := by
    intro y hy
    by_contra hne
    have h1 : f y ≠ 0 := left_ne_zero_of_mul hne
    have h2 : f (y - t) ≠ 0 := right_ne_zero_of_mul hne
    have a1 : |y| ≤ L / 2 := not_lt.mp fun h => h1 (hs y h)
    have a2 : |y - t| ≤ L / 2 := not_lt.mp fun h => h2 (hs _ h)
    apply hy
    simp only [hS, mem_Icc]
    refine ⟨?_, (abs_le.mp a1).2⟩
    linarith [(abs_le.mp a2).1]
  set a : ℝ → ℝ := S.indicator fun y => f y ^ 2 with ha
  set b : ℝ → ℝ := S.indicator fun y => f (y - t) ^ 2 with hb
  have hai : Integrable a := hsq.indicator hSm
  have hbi : Integrable b := hsh.indicator hSm
  have hbound : ∀ y, |f y * f (y - t)| ≤ (a y + b y) / 2 := by
    intro y
    by_cases hy : y ∈ S
    · simp only [ha, hb, indicator_of_mem hy]
      rw [abs_mul]
      nlinarith [sq_nonneg (|f y| - |f (y - t)|), sq_abs (f y), sq_abs (f (y - t))]
    · rw [hsupp y hy]
      simp only [ha, hb, indicator_of_notMem hy]
      simp
  have h1 : |autocorr f t| ≤ ∫ y, (a y + b y) / 2 := by
    unfold autocorr
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hai.add hbi).div_const 2)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hbound y
  rw [integral_div, integral_add hai hbi] at h1
  -- ∫ a = ∫_S f²
  have e1 : ∫ y, a y = ∫ y in S, f y ^ 2 := integral_indicator hSm
  -- ∫ b = ∫_{S'} f²
  have e2 : ∫ y, b y = ∫ y in S', f y ^ 2 := by
    rw [← integral_indicator hS'm]
    have : b = fun y => (S'.indicator fun x => f x ^ 2) (y - t) := by
      funext y
      simp only [hb]
      by_cases hy : y ∈ S
      · have hy' : y - t ∈ S' := by
          simp only [hS, hS', mem_Icc] at hy ⊢
          constructor <;> linarith [hy.1, hy.2]
        simp [indicator_of_mem hy, indicator_of_mem hy']
      · have hy' : y - t ∉ S' := by
          simp only [hS, hS', mem_Icc, not_and_or, not_le] at hy ⊢
          rcases hy with h | h
          · left; linarith
          · right; linarith
        simp [indicator_of_notMem hy, indicator_of_notMem hy']
    rw [this]
    exact integral_sub_right_eq_self (fun x => (S'.indicator fun x => f x ^ 2) x) t
  have e3 : (∫ y in S', f y ^ 2) + ∫ y in S, f y ^ 2 ≤ ∫ y, f y ^ 2 := by
    rw [← setIntegral_union hdisj hSm hsq.integrableOn hsq.integrableOn]
    exact setIntegral_le_integral hsq (Filter.Eventually.of_forall fun y => sq_nonneg _)
  rw [GppRungZeroPositivity.autocorr_zero_eq]
  rw [e1, e2] at h1
  linarith

end GppShiftPresentation

#print axioms GppShiftPresentation.abs_autocorr_le_half
