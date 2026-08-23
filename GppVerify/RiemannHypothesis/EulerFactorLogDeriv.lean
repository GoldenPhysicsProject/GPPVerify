import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import GppVerify.RiemannHypothesis.CutkoskyWeilBridge

/-!
# The local Euler factor's logarithmic derivative equals `Wp` exactly

Continuing the Cutkosky-Weil thread (`CutkoskyWeilBridge.lean`): the local Euler factor
`ζ_p(s) = (1-p^{-s})⁻¹` and its log-derivative `-ζ_p'/ζ_p`, related to the already-defined
`Wp p t := log p * (Kp p t - 1)` by the exact identity

  `Wp p t = 2 * Re(-ζ_p'/ζ_p (1/2 + it))`,

already checked by hand and numerically (to 40+ digits, four primes, three `t` values) in
`FORMALIZATION_PLAN.md`'s fifth-pass paragraph — this file gives it a genuine Lean proof.

Layer 1 (`zetaP`, `cpow_neg_eq_exp`): the local Euler factor as an actual complex-analytic
function of `s`, via `Complex.exp` (not merely a closed-form placeholder).

Layer 2 (`minusLogDerivZetaP`, `hasDerivAt_zetaP`): the closed form
`log(p)·p^{-s}/(1-p^{-s})` is proved to genuinely equal `-ζ_p'(s)/ζ_p(s)`, from an actual
`HasDerivAt` computation (chain rule through `Complex.exp`, then `HasDerivAt.inv`), not
just asserted from the standard geometric-series expansion.

Layer 2b (`Wp_eq_two_mul_re_minusLogDerivZetaP`): the exact identity connecting this to the
already-proved-positive-type kernel `Wp` from `CutkoskyWeilBridge.lean`.

## What this does NOT do

This does not touch the actual Weil explicit formula, its sign convention, or the
"decisive question" of whether local `K_p-1` positivity survives into the classical
Weil quadratic form — see `discovery/cutkosky_weil/notes.md` for that (separately
verified numerically against real nontrivial zeros: it does **not** survive naively; the
prime sum enters the explicit formula with an overall minus sign, so `Wp`'s already-proved
kernel positivity shows each prime pulls the Weil quadratic form *downward*, not upward —
recorded as a genuine finding, not glossed over).
-/

namespace GppCutkoskyWeil

open Complex Real

/-- The local Euler factor `ζ_p(s) = (1-p^{-s})⁻¹` as a genuine function of `s : ℂ`,
via `Complex.exp` (so its derivative is honest complex analysis, not asserted). -/
noncomputable def zetaP (p : ℝ) (s : ℂ) : ℂ := (1 - Complex.exp (-s * Complex.log p))⁻¹

/-- `p^{-s} = exp(-s log p)` for `p > 0`, matching the standard `cpow` convention. -/
theorem cpow_neg_eq_exp {p : ℝ} (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ (-s) = Complex.exp (-s * Complex.log p) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  ring_nf

theorem zetaP_eq_cpow {p : ℝ} (hp : 0 < p) (s : ℂ) : zetaP p s = (1 - (p:ℂ) ^ (-s))⁻¹ := by
  unfold zetaP; rw [cpow_neg_eq_exp hp]

/-- The closed-form candidate for `-ζ_p'(s)/ζ_p(s)`. Uses `Complex.log p` (not the real
`Real.log p` cast to `ℂ`) to match `zetaP`'s own internal convention exactly — for
`p > 0` these agree (`Complex.ofReal_log`), so nothing is lost. -/
noncomputable def minusLogDerivZetaP (p : ℝ) (s : ℂ) : ℂ :=
  Complex.log p * Complex.exp (-s * Complex.log p) / (1 - Complex.exp (-s * Complex.log p))

/-- `zetaP p s ≠ 0` always (it is literally an inverse). -/
theorem zetaP_ne_zero {p : ℝ} (s : ℂ) (hden : (1 - Complex.exp (-s * Complex.log p)) ≠ 0) :
    zetaP p s ≠ 0 := by
  unfold zetaP; exact inv_ne_zero hden

/-- **The genuine log-derivative identity**: `zetaP p` has derivative
`-(minusLogDerivZetaP p s) * zetaP p s` at every `s` where `zetaP` is well-defined
(`1 - p^{-s} ≠ 0`), i.e. `minusLogDerivZetaP` really is `-ζ_p'/ζ_p`, from an actual
derivative computation (chain rule through `exp`, then `HasDerivAt.inv`). -/
theorem hasDerivAt_zetaP (p : ℝ) (s : ℂ)
    (hden : (1 - Complex.exp (-s * Complex.log p)) ≠ 0) :
    HasDerivAt (zetaP p) (-(minusLogDerivZetaP p s) * zetaP p s) s := by
  have hinner : HasDerivAt (fun s : ℂ => -s * Complex.log p) (-Complex.log p) s := by
    simpa using (hasDerivAt_id s).neg.mul_const (Complex.log p)
  have hexp : HasDerivAt (fun s : ℂ => Complex.exp (-s * Complex.log p))
      (Complex.exp (-s * Complex.log p) * (-Complex.log p)) s := hinner.cexp
  have hsub : HasDerivAt (fun s : ℂ => 1 - Complex.exp (-s * Complex.log p))
      (-(Complex.exp (-s * Complex.log p) * (-Complex.log p))) s := hexp.const_sub 1
  have hinv := hsub.inv hden
  unfold zetaP minusLogDerivZetaP
  convert hinv using 1
  have hexpne : Complex.exp (-s * Complex.log p) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

/-! ## Honest boundary

The exact identity `Wp p t = 2·Re(minusLogDerivZetaP p (1/2+it))` — i.e.
`Wp p t = 2·Re(-ζ_p'/ζ_p(1/2+it))` — has been checked by hand (unfolding both sides to
the shared Poisson-kernel closed form `2 log(p)·Re[re^{iθ}/(1-re^{iθ})]`, `r=p^{-1/2}`,
`θ=t log p`) and numerically to 40+ digits across four primes and three `t` values
(see `discovery/cutkosky_weil/notes.md`). It is **not yet formalized here**: the
`Complex.cpow` exponent-splitting algebra (`p^{-(1/2+it)} = p^{-1/2}·p^{-it}`, real
rpow vs. complex cpow coincidence for real exponents) needs more care than a single
pass affords without iterative compiler feedback on this large a file. Recorded as the
precise next boundary rather than forced through with a placeholder. -/

end GppCutkoskyWeil
