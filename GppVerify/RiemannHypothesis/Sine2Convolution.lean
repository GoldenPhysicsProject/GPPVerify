import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Midpoint symmetry turns the sine² convolution into the shifted autocorrelation

Source: Codex, GPP-bridge PR #11 comment 6377118601 (prime–pole cancellation on Arch-dark
vectors). Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and
Claude Code (formalization).

Let `G(t) = ∫ f(u) f(u + t) du` be the autocorrelation of a function `f : ℝ → ℝ`.

* `autocorr_neg`: `G(−t) = G(t)` (translation invariance of Lebesgue measure).
* `conv_eq_autocorr`: if `f(1 − x) = f(x)` for all `x`, then
  `(f ∗ f)(s) = ∫ f(u) f(s − u) du = G(s − 1)`.
* `bump_symm`: the sine² bump `b(u) = sin²(πu) 1_{[0,1]}(u)` is symmetric about `1/2`, so
  `bump_conv_eq_autocorr`: `(b ∗ b)(s) = G₀(s − 1)` with `G₀` the autocorrelation of `b`. This is
  the step Codex uses to rewrite the sewn prime kernel as an ordinary convolution `V_K ∗ V_K`.

**Scope.** The pointwise identity only, with the integrals as Bochner integrals (no
integrability hypotheses are needed for the equalities). The identities
`∫ e^{t/2} C_V = A_K²` and the parity split `P^± = E_K ± (C_K − ε_K)` are not formalized.
No claim about RH.
-/

open Real MeasureTheory Set

namespace GppSine2Convolution

/-- The autocorrelation `G(t) = ∫ f(u) f(u + t) du`. -/
noncomputable def autocorr (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u, f u * f (u + t)

/-- **The autocorrelation is even.** -/
theorem autocorr_neg (f : ℝ → ℝ) (t : ℝ) : autocorr f (-t) = autocorr f t := by
  unfold autocorr
  have h := integral_add_right_eq_self (μ := volume) (fun u => f u * f (u + -t)) t
  simp only [add_neg_cancel_right] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only; ring_nf)

/-- **Midpoint symmetry turns convolution into the shifted autocorrelation.** -/
theorem conv_eq_autocorr (f : ℝ → ℝ) (hf : ∀ x, f (1 - x) = f x) (s : ℝ) :
    ∫ u, f u * f (s - u) = autocorr f (s - 1) := by
  rw [← autocorr_neg]
  unfold autocorr
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← hf (s - u)]
  ring_nf

/-- The sine² bump `b(u) = sin²(πu) 1_{[0,1]}(u)`. -/
noncomputable def bump (u : ℝ) : ℝ := (Icc (0 : ℝ) 1).indicator (fun x => sin (π * x) ^ 2) u

/-- **The bump is symmetric about `1/2`.** -/
theorem bump_symm (x : ℝ) : bump (1 - x) = bump x := by
  unfold bump
  have hmem : (1 - x ∈ Icc (0 : ℝ) 1) ↔ x ∈ Icc (0 : ℝ) 1 := by
    simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx, mul_sub, mul_one, sin_pi_sub]
  · rw [indicator_of_notMem (fun h => hx (hmem.mp h)), indicator_of_notMem hx]

/-- **`(b ∗ b)(s) = G₀(s − 1)`** for the sine² bump. -/
theorem bump_conv_eq_autocorr (s : ℝ) :
    ∫ u, bump u * bump (s - u) = autocorr bump (s - 1) :=
  conv_eq_autocorr bump bump_symm s

end GppSine2Convolution
