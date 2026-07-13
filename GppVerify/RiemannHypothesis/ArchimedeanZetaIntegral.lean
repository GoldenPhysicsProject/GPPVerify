import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The archimedean local zeta integral

Tate's thesis needs a local factor at every place of `ℚ`, including the archimedean
place `ℝ`. For the standard Gaussian test function `Φ(x) = e^{-πx²}`, the archimedean
local zeta integral (in the multiplicative-measure convention `d^×x = dx/‖x‖`, matching
the normalization used throughout this thread's p-adic files) is the classical identity

`∫_ℝ e^{-πx²} · |x|^{s-1} dx = π^{-s/2} · Γ(s/2)`, for every real `s > 0`.

Independently checked via `sympy.integrate` before writing this file (confirming
`∫_0^∞ e^{-πx²}x^{s-1}dx = (1/2)π^{-s/2}Γ(s/2)`, hence twice that over all of `ℝ` by
evenness). Proved here purely from two Mathlib lemmas already available for the
half-line Gaussian-Gamma integral (`integral_rpow_mul_exp_neg_mul_rpow`,
`Mathlib.MeasureTheory.Integral.Gamma`) plus the even-function doubling identity
`integral_comp_abs` (`Mathlib.MeasureTheory.Measure.Lebesgue.Integral`) — no new axioms,
no numerical approximation.

Not sourced from a specific Golden Physics Project paper.
-/

namespace GppArchimedeanZeta

open MeasureTheory

/-- **The archimedean local zeta integral**: `∫_ℝ e^{-πx²}|x|^{s-1} dx = π^{-s/2}Γ(s/2)`,
    for every real `s > 0` — Tate's-thesis local factor at the real place. -/
theorem archimedean_zeta_integral (s : ℝ) (hs : 0 < s) :
    ∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * |x| ^ (s - 1) =
      Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2) := by
  -- `integral_comp_abs`'s statement, specialized to our integrand and beta-reduced by
  -- `have`'s defeq check (avoiding the beta-redex `rw` would otherwise have to match).
  have hdouble :
      (∫ x : ℝ, Real.exp (-Real.pi * |x| ^ 2) * |x| ^ (s - 1)) =
        2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-Real.pi * x ^ 2) * x ^ (s - 1) :=
    integral_comp_abs (f := fun y : ℝ => Real.exp (-Real.pi * y ^ 2) * y ^ (s - 1))
  -- A plain `simp_rw [← sq_abs]` loops forever here: after rewriting `x ^ 2` to
  -- `|x| ^ 2`, that result *itself* matches `sq_abs`'s generic `?a ^ 2` pattern again
  -- (with `?a := |x|`), so the fixpoint-seeking rewrite never stops. Using a single
  -- fully-formed pointwise equation instead terminates after exactly one rewrite.
  have hpt : ∀ x : ℝ, Real.exp (-Real.pi * x ^ 2) * |x| ^ (s - 1) =
      Real.exp (-Real.pi * |x| ^ 2) * |x| ^ (s - 1) := fun x => by rw [← sq_abs]
  simp_rw [hpt]
  rw [hdouble]
  have hcomm :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-Real.pi * x ^ 2) * x ^ (s - 1)) =
        ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) * Real.exp (-Real.pi * x ^ 2) := by
    congr 1
    funext x
    ring
  rw [hcomm]
  -- `integral_rpow_mul_exp_neg_mul_rpow`'s `x ^ p` is `Real.rpow` (since `p : ℝ`), but
  -- our `x ^ 2` above is the natural-number `Monoid.npow` (from the literal `2` in the
  -- theorem statement) — same value, different underlying function, so `rw` can't see
  -- them as the same pattern until this is bridged explicitly.
  have hpow2 : ∀ x : ℝ, x ^ (2 : ℕ) = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [hpow2]
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s - 1) (b := Real.pi)
        (by norm_num) (by linarith) Real.pi_pos]
  have hexp : s - 1 + 1 = s := by ring
  rw [hexp]
  ring

end GppArchimedeanZeta
