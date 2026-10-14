import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact autocorrelation of the sharp odd mirror window `sinh(t/2)·1_{[−h,h]}`

Source: Codex, GPP-bridge `work/codex/2026-10-14_odd_mirror_full_signed_weil_window.md`
(da2359b3; PR #11 comment 6163819485); reproduction in GPPDiscovery2
`research/codex/compact_sewing_20261014/odd_mirror_full_weil.py`.

For the odd window `g = sinh(t/2)` on `[−h, h]`, the overlap `∫ g(s) g(s+t) ds` over
`s ∈ [−h, h − t]` is `sinh(h − t/2) − (h − t/2) cosh(t/2)` (`autocorr`). Divided by
`N_h = sinh h − h` (`TwoFacePoleSignature.norm_sinh_half`) this is Codex's `F_h(t)`. It is the
input to the full signed Weil evaluation `Q_h = P_h − W_ℝ − W_p`. At `h = 4`, Claude Code's
independent mpmath check reproduces `Q_4 = +0.0698371091`, and Codex's Abel/Chebyshev identity
to about `10⁻¹⁴`. `Q_h` is numerically positive for `h = 1, …, 8` (not certified). Positivity of
`Q_h` for one test family is a witness consistent with RH, not a proof. **No RH claim.**
-/

namespace GppOddWindowAutocorrelation

open Real

theorem sinh_mul_sinh (a b : ℝ) : sinh a * sinh b = (cosh (a + b) - cosh (a - b)) / 2 := by
  rw [cosh_add, cosh_sub]; ring

/-- **Exact autocorrelation** of the sharp odd window. -/
theorem autocorr (h t : ℝ) :
    ∫ s in (-h)..(h - t), sinh (s / 2) * sinh ((s + t) / 2) =
      sinh (h - t / 2) - (h - t / 2) * cosh (t / 2) := by
  have hint : ∀ s, sinh (s / 2) * sinh ((s + t) / 2) = (cosh (s + t / 2) - cosh (t / 2)) / 2 := by
    intro s
    rw [sinh_mul_sinh]
    congr 2 <;> [ring_nf; (rw [← cosh_neg]; ring_nf)]
  simp_rw [hint]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => (sinh (s + t / 2) - s * cosh (t / 2)) / 2)
    (fun x _ => by
      have h1 := ((hasDerivAt_id' x).add_const (t / 2)).sinh
      have h2 := (hasDerivAt_id' x).mul_const (cosh (t / 2))
      refine ((h1.sub h2).div_const 2).congr_deriv ?_
      simp)
    ((by fun_prop : Continuous fun s : ℝ => (cosh (s + t / 2) - cosh (t / 2)) / 2).intervalIntegrable
      (-h) (h - t))]
  have e : -h + t / 2 = -(h - t / 2) := by ring
  rw [show h - t + t / 2 = h - t / 2 by ring, e, sinh_neg]
  ring

/-- The window's overlap vanishes at the support edge `t = 2h`. -/
theorem autocorr_edge (h : ℝ) : sinh (h - 2 * h / 2) - (h - 2 * h / 2) * cosh (2 * h / 2) = 0 := by
  rw [show h - 2 * h / 2 = 0 by ring]; simp

end GppOddWindowAutocorrelation
