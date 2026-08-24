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

This does not prove the global Weil explicit formula or its positivity.  The local sign
question can, however, be settled exactly: the prime term carries an overall minus sign,
but `K_p-1` being positive-type as a convolution kernel does **not** make multiplication by
`-Wp` negative semidefinite.  The two operators are different.  The final section proves
that `Wp` has the expected prime-power Fourier expansion and that the signed scalar
multiplier `-Wp` takes both signs.  Consequently a global proof must use the test-function
transform and the Archimedean/prime coupling; it cannot stack same-signed local operators.
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

/-! ## Prime powers and the exact local sign obstruction

The positive-type theorem in `CutkoskyWeilBridge.lean` concerns **convolution** by
`K_p-1`: its Fourier eigenvalues are the nonnegative numbers `p^{-|n|/2}`.  The classical
finite-prime term instead inserts the scalar function with the opposite sign into a
test-function pairing.  Pointwise multiplication and convolution are not the same
operator.  The layers below make the distinction explicit and machine-check it:

* `WpFourierTerm` is the two-sided prime-power expansion of `Wp`;
* every nonzero Fourier coefficient is positive;
* nevertheless `Wp` itself is positive at phase zero and negative at the antipodal phase;
* hence the signed multiplier `-Wp` changes sign.

This is a local obstruction, not a negative result about the global Weil form.  It says
precisely that the missing prime--Archimedean/test-transform bridge must do genuine work.
-/

/-- The vacuum-subtracted Poisson kernel at phase zero.  Only `r < 1` is needed. -/
theorem KrClosed_sub_one_zero {r : ℝ} (hr1 : r < 1) :
    KrClosed r 0 - 1 = 2 * r / (1 - r) := by
  unfold KrClosed
  rw [Real.cos_zero]
  have hne : 1 - r ≠ 0 := by linarith
  have hden : 1 - 2 * r * 1 + r ^ 2 = (1 - r) ^ 2 := by ring
  rw [hden]
  field_simp
  ring

/-- The vacuum-subtracted Poisson kernel at the antipodal phase `π`. -/
theorem KrClosed_sub_one_pi {r : ℝ} (hr0 : 0 ≤ r) :
    KrClosed r Real.pi - 1 = -(2 * r / (1 + r)) := by
  unfold KrClosed
  rw [Real.cos_pi]
  have hne : 1 + r ≠ 0 := by linarith
  have hden : 1 - 2 * r * (-1) + r ^ 2 = (1 + r) ^ 2 := by ring
  rw [hden]
  field_simp
  ring

/-- `Wp` is strictly positive at phase zero for every real `p > 1`. -/
theorem Wp_zero_pos {p : ℝ} (hp : 1 < p) : 0 < Wp p 0 := by
  have hp0 : 0 < p := lt_trans one_pos hp
  let r : ℝ := p ^ (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hrpos : 0 < r := Real.rpow_pos_of_pos hp0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hlog : 0 < Real.log p := Real.log_pos hp
  unfold Wp
  rw [Kp_eq_KrClosed hp, show 0 * Real.log p = 0 by ring,
    KrClosed_sub_one_zero hr1]
  exact mul_pos hlog (div_pos (by positivity) (sub_pos.mpr hr1))

/-- `Wp` is strictly negative when its phase is `π`.  This is the first exact witness that
positive-type convolution does not imply pointwise nonnegativity. -/
theorem Wp_antiphase_neg {p : ℝ} (hp : 1 < p) :
    Wp p (Real.pi / Real.log p) < 0 := by
  have hp0 : 0 < p := lt_trans one_pos hp
  let r : ℝ := p ^ (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hrpos : 0 < r := Real.rpow_pos_of_pos hp0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hphase : Real.pi / Real.log p * Real.log p = Real.pi := by
    field_simp
  unfold Wp
  rw [Kp_eq_KrClosed hp, hphase, KrClosed_sub_one_pi hr0]
  exact mul_neg_of_pos_of_neg hlog
    (neg_neg_of_pos (div_pos (by positivity) (by positivity)))

/-- The coefficient of the `n`th two-sided prime-power mode.  The zero mode is recorded by
this coefficient function but omitted by `WpFourierTerm`, implementing vacuum subtraction. -/
noncomputable def primePowerCoeff (p : ℝ) (n : ℤ) : ℝ :=
  Real.log p * (p ^ (-(1 : ℝ) / 2)) ^ n.natAbs

/-- The frequency of the `n`th prime-power mode. -/
noncomputable def primePowerFrequency (p : ℝ) (n : ℤ) : ℝ :=
  n * Real.log p

/-- The vacuum-subtracted two-sided Fourier term for `Wp`. -/
noncomputable def WpFourierTerm (p t : ℝ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else
    (Real.log p : ℂ) *
      (((p ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) ^ n.natAbs *
        Complex.exp (Complex.I * (n : ℂ) * ((t * Real.log p : ℝ) : ℂ)))

/-- Each nonzero term is exactly its prime-power coefficient times its frequency phase. -/
theorem WpFourierTerm_eq_coeff_frequency {p t : ℝ} {n : ℤ} (hn : n ≠ 0) :
    WpFourierTerm p t n =
      (primePowerCoeff p n : ℂ) *
        Complex.exp (Complex.I * (primePowerFrequency p n * t : ℝ)) := by
  simp only [WpFourierTerm, primePowerCoeff, primePowerFrequency,
    if_neg hn, Complex.ofReal_mul]
  push_cast
  ring

/-- The normalized half-power raised to `m` is the expected `p^{-m/2}`. -/
theorem rpow_neg_half_pow {p : ℝ} (hp0 : 0 ≤ p) (m : ℕ) :
    (p ^ (-(1 : ℝ) / 2)) ^ m = p ^ (-(m : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
  congr 1
  ring

/-- Closed form of the coefficient: `log p · p^{-|n|/2}`. -/
theorem primePowerCoeff_eq {p : ℝ} (hp0 : 0 ≤ p) (n : ℤ) :
    primePowerCoeff p n = Real.log p * p ^ (-(n.natAbs : ℝ) / 2) := by
  unfold primePowerCoeff
  rw [rpow_neg_half_pow hp0]

/-- Every prime-power Fourier coefficient is strictly positive for `p > 1`. -/
theorem primePowerCoeff_pos {p : ℝ} (hp : 1 < p) (n : ℤ) :
    0 < primePowerCoeff p n := by
  unfold primePowerCoeff
  exact mul_pos (Real.log_pos hp)
    (pow_pos (Real.rpow_pos_of_pos (lt_trans one_pos hp) _) _)

/-- Absolute summability of the two-sided prime-power expansion. -/
theorem summable_WpFourierTerm {p : ℝ} (hp : 1 < p) (t : ℝ) :
    Summable (WpFourierTerm p t) := by
  have hp0 : 0 < p := lt_trans one_pos hp
  let r : ℝ := p ^ (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hs := summable_KrClosed_summand hr0 hr1 (t * Real.log p)
  have hmul := hs.mul_left (Real.log p : ℂ)
  apply hmul.congr
  intro n
  by_cases hn : n = 0 <;> simp [WpFourierTerm, r, hn]

/-- **Exact prime-power expansion**:
`Wp(p,t) = Σ_{n∈ℤ\{0}} log(p) p^{-|n|/2} exp(i n t log p)`.
The theorem is an equality of an absolutely summable complex series with the real scalar
`Wp` embedded in `ℂ`. -/
theorem tsum_WpFourierTerm_eq {p : ℝ} (hp : 1 < p) (t : ℝ) :
    ∑' n : ℤ, WpFourierTerm p t n = (Wp p t : ℂ) := by
  have hp0 : 0 < p := lt_trans one_pos hp
  let r : ℝ := p ^ (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  let base : ℤ → ℂ := fun n => if n = 0 then 0 else
    (r : ℂ) ^ n.natAbs *
      Complex.exp (Complex.I * (n : ℂ) * ((t * Real.log p : ℝ) : ℂ))
  have hs : Summable base := by
    exact summable_KrClosed_summand hr0 hr1 (t * Real.log p)
  have hfun : WpFourierTerm p t = fun n => (Real.log p : ℂ) * base n := by
    funext n
    by_cases hn : n = 0 <;> simp [WpFourierTerm, base, r, hn]
  rw [hfun, hs.tsum_mul_left]
  have hsum := tsum_KrClosed_summand_eq hr0 hr1 (t * Real.log p)
  change (∑' n : ℤ, base n) = ((KrClosed r (t * Real.log p) : ℝ) : ℂ) - 1 at hsum
  rw [hsum]
  unfold Wp
  rw [Kp_eq_KrClosed hp]
  change (Real.log p : ℂ) *
      (↑(KrClosed (p ^ (-(1 : ℝ) / 2)) (t * Real.log p)) - 1) =
    ↑(Real.log p * (KrClosed (p ^ (-(1 : ℝ) / 2)) (t * Real.log p) - 1))
  push_cast
  rfl

/-- The signed scalar local term with the conventional overall minus sign.  Naming this
function does not assert the global explicit formula; that transform remains a separate
bridge. -/
noncomputable def weilPrimeMultiplier (p t : ℝ) : ℝ := -Wp p t

/-- The signed local multiplier is the negative real part of the genuine Euler-factor
logarithmic derivative. -/
theorem weilPrimeMultiplier_eq_neg_two_mul_re_minusLogDerivZetaP
    {p : ℝ} (hp : 1 < p) (t : ℝ) :
    weilPrimeMultiplier p t =
      -2 * (minusLogDerivZetaP p (1 / 2 + t * Complex.I)).re := by
  unfold weilPrimeMultiplier
  rw [Wp_eq_two_mul_re_minusLogDerivZetaP hp]
  ring

/-- The signed multiplier is negative at phase zero. -/
theorem weilPrimeMultiplier_zero_neg {p : ℝ} (hp : 1 < p) :
    weilPrimeMultiplier p 0 < 0 := by
  unfold weilPrimeMultiplier
  exact neg_neg_of_pos (Wp_zero_pos hp)

/-- The same signed multiplier is positive at the antipodal phase. -/
theorem weilPrimeMultiplier_antiphase_pos {p : ℝ} (hp : 1 < p) :
    0 < weilPrimeMultiplier p (Real.pi / Real.log p) := by
  unfold weilPrimeMultiplier
  exact neg_pos.mpr (Wp_antiphase_neg hp)

/-- **Exact local obstruction**: for every `p > 1`, the signed prime multiplier takes both
signs.  Therefore it is neither a pointwise-positive nor a pointwise-negative channel,
despite the nonnegative Fourier coefficients of its unsigned positive-type kernel. -/
theorem weilPrimeMultiplier_sign_changes {p : ℝ} (hp : 1 < p) :
    ∃ tNeg tPos : ℝ,
      weilPrimeMultiplier p tNeg < 0 ∧ 0 < weilPrimeMultiplier p tPos := by
  exact ⟨0, Real.pi / Real.log p,
    weilPrimeMultiplier_zero_neg hp,
    weilPrimeMultiplier_antiphase_pos hp⟩

end GppCutkoskyWeil
