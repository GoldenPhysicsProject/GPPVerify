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

/-! ## The connection to `Wp`, closed

Seventh pass: the identity flagged above as the "honest next boundary" — now proved. -/

/-- **The real Poisson-kernel identity behind `Kp_eq_KrClosed`**: for real `r, θ` with
`0 ≤ r < 1`, `KrClosed r θ - 1 = 2·Re[r·e^{iθ}/(1-r·e^{iθ})]`. The `r < 1` bound is genuinely
needed (not just convenient): at `r = 1, θ = 0` the denominator `1 - r·e^{iθ}` vanishes and
Lean's total division sends both sides to different junk values, so the identity is false
without it — matching the only case that actually arises (`r = p^{-1/2} < 1` for `p > 1`). -/
theorem KrClosed_sub_one_eq_two_mul_re {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    KrClosed r θ - 1 =
      2 * ((r : ℂ) * Complex.exp (θ * Complex.I) /
        (1 - (r : ℂ) * Complex.exp (θ * Complex.I))).re := by
  have hzre : ((r : ℂ) * Complex.exp (θ * Complex.I)).re = r * Real.cos θ := by
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hzim : ((r : ℂ) * Complex.exp (θ * Complex.I)).im = r * Real.sin θ := by
    simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hdre : ((1:ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)).re = 1 - r * Real.cos θ := by
    rw [Complex.sub_re, Complex.one_re, hzre]
  have hdim : ((1:ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)).im = -(r * Real.sin θ) := by
    rw [Complex.sub_im, Complex.one_im, hzim]; ring
  rw [Complex.div_re, Complex.normSq_apply, hzre, hzim, hdre, hdim]
  unfold KrClosed
  have h1r : (0:ℝ) < 1 - r := by linarith
  have h1cos : (0:ℝ) ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hdenpos : (0:ℝ) < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    nlinarith [mul_pos h1r h1r, mul_nonneg hr0 h1cos]
  have hdeneq : (1 - r * Real.cos θ) * (1 - r * Real.cos θ) + -(r * Real.sin θ) * -(r * Real.sin θ)
      = 1 - 2 * r * Real.cos θ + r ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hdeneq]
  field_simp
  linear_combination 2 * r ^ 2 * Real.sin_sq_add_cos_sq θ

/-- `p^{-1/2}` (real `rpow`) equals `Real.exp(-(1/2) * log p)` for `p > 0` — the standard
`rpow` closed form, needed to split the complex exponential below. -/
theorem rpow_neg_half_eq_exp {p : ℝ} (hp : 0 < p) :
    p ^ (-(1:ℝ)/2) = Real.exp (-(1/2) * Real.log p) := by
  rw [Real.rpow_def_of_pos hp]; ring_nf

/-- **The exact identity, closed**: `Wp p t = 2·Re(minusLogDerivZetaP p (1/2+it))`, i.e.
`Wp p t = 2·Re(-ζ_p'/ζ_p(1/2+it))`. Proved by splitting the exponential at `s=1/2+it`
into its real (`p^{-1/2}`) and imaginary (`e^{-it log p}`) pieces, using the conjugation
symmetry `Re[r e^{-iθ}/(1-r e^{-iθ})] = Re[r e^{iθ}/(1-r e^{iθ})]` for real `r`, and
`KrClosed_sub_one_eq_two_mul_re` above. -/
theorem Wp_eq_two_mul_re_minusLogDerivZetaP {p : ℝ} (hp : 1 < p) (t : ℝ) :
    Wp p t = 2 * (minusLogDerivZetaP p (1/2 + t * Complex.I)).re := by
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  set θ : ℝ := t * Real.log p with hθdef
  set r : ℝ := p ^ (-(1:ℝ)/2) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; exact Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := by rw [hrdef]; exact Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hlogpC : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_log hp0.le).symm
  have hrexp : r = Real.exp (-(1/2) * Real.log p) := by rw [hrdef]; exact rpow_neg_half_eq_exp hp0
  clear_value r θ
  have hlogp_re : (Complex.log (p : ℂ)).re = Real.log p := Complex.log_ofReal_re p
  have hlogp_im : (Complex.log (p : ℂ)).im = 0 := by rw [hlogpC]; exact Complex.ofReal_im _
  -- Step 1: real/imaginary parts of the exponent w = -(1/2+it) log p
  have hwre : (-(1/2 + t * Complex.I) * Complex.log p).re = -(1/2) * Real.log p := by
    rw [Complex.mul_re, hlogp_re, hlogp_im]; simp
  have hwim : (-(1/2 + t * Complex.I) * Complex.log p).im = -θ := by
    rw [Complex.mul_im, hlogp_re, hlogp_im, hθdef]; simp
  -- Step 2: real/imaginary parts of exp(w), via Complex.exp_re / exp_im
  have hEre : (Complex.exp (-(1/2 + t * Complex.I) * Complex.log p)).re = r * Real.cos θ := by
    rw [Complex.exp_re, hwre, hwim, ← hrexp, Real.cos_neg]
  have hEim : (Complex.exp (-(1/2 + t * Complex.I) * Complex.log p)).im = -(r * Real.sin θ) := by
    rw [Complex.exp_im, hwre, hwim, ← hrexp, Real.sin_neg]; ring
  -- Step 3: real/imaginary parts of numerator (log p * exp w) and denominator (1 - exp w)
  have hNre : (Complex.log p * Complex.exp (-(1/2 + t * Complex.I) * Complex.log p)).re
      = Real.log p * (r * Real.cos θ) := by
    rw [Complex.mul_re, hlogp_re, hlogp_im, hEre]; ring
  have hNim : (Complex.log p * Complex.exp (-(1/2 + t * Complex.I) * Complex.log p)).im
      = Real.log p * -(r * Real.sin θ) := by
    rw [Complex.mul_im, hlogp_re, hlogp_im, hEim]; ring
  have hDre : (1 - Complex.exp (-(1/2 + t * Complex.I) * Complex.log p)).re = 1 - r * Real.cos θ := by
    rw [Complex.sub_re, Complex.one_re, hEre]
  have hDim : (1 - Complex.exp (-(1/2 + t * Complex.I) * Complex.log p)).im = r * Real.sin θ := by
    rw [Complex.sub_im, Complex.one_im, hEim]; ring
  -- Step 4: assemble via Complex.div_re, then close as real algebra using Kp_eq_KrClosed
  unfold minusLogDerivZetaP
  rw [Complex.div_re, Complex.normSq_apply, hNre, hNim, hDre, hDim]
  unfold Wp
  rw [Kp_eq_KrClosed hp t]
  unfold KrClosed
  rw [← hrdef, ← hθdef]
  have h1r : (0:ℝ) < 1 - r := by linarith
  have h1cos : (0:ℝ) ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hdenpos : (0:ℝ) < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    nlinarith [mul_pos h1r h1r, mul_nonneg hr0 h1cos]
  have hdeneq : (1 - r * Real.cos θ) * (1 - r * Real.cos θ) + (r * Real.sin θ) * (r * Real.sin θ)
      = 1 - 2 * r * Real.cos θ + r ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hdeneq]
  field_simp
  linear_combination (Real.log p) * (2 * r ^ 2) * Real.sin_sq_add_cos_sq θ

end GppCutkoskyWeil
