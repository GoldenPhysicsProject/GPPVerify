import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GppVerify.QuantumGravity.GammaModulusIdentity

/-!
# The logistic Fourier pair

From `Modular_Thermality_of_the_Celestial_Spectral_Weight.tex` and
`Spectral_Weight_from_Principal_Series.tex`: the celestial spectral weight
`P(λ) = πλ/sinh(πλ)` (already proved in closed form in `PlanckForm.lean`, `MatsubaraPoles.lean`)
is the Fourier transform of the logistic density,

  `∫ℝ e^{iλx} / (4 cosh²(x/2)) dx = πλ / sinh(πλ)`.     (`logistic_fourier_pair`)

## The route: Beta integral and Euler reflection

Substitute the logistic distribution function `u = σ(x) = 1/(1+e^{-x})`. Its density is exactly
the integrand's weight, `σ'(x) = 1/(4cosh²(x/2))` (`weight_eq_sech_sq`), and `σ/(1−σ) = eˣ`, so
the character `e^{iλx}` becomes `u^{iλ}(1−u)^{−iλ}` (`beta_kernel_logistic`). Hence

  `∫ℝ e^{iλx} σ'(x) dx = ∫₀¹ u^{iλ}(1−u)^{−iλ} du = B(1+iλ, 1−iλ) = Γ(1+iλ)Γ(1−iλ)`,

and `Γ(1+iλ)Γ(1−iλ) = iλ·Γ(iλ)Γ(1−iλ) = iλπ/sin(iπλ) = πλ/sinh(πλ)` by Euler reflection.
This is also the physics: `P(λ) = Γ(1+iλ)Γ(1−iλ)` is the two-particle phase-space factor.

The last equality is not proved here. It is `GppGammaModulus.gamma_one_add_mul_gamma_one_sub`,
already in `GammaModulusIdentity.lean`, and is reused. The only new link this file supplies is
the substitution showing the Fourier integral *is* the Beta integral.

## Why this stub was parked, and why that verdict was wrong

This file was a `True`-stub from 2026-08 to 2026-09-26, recorded as "genuinely attempted,
confirmed out of reach" and "a substantially larger, multi-file undertaking … not a same-session
item." The census behind that verdict was accurate at Mathlib v4.19.0 — zero occurrences of
`sech`, no closed-form Fourier transform beyond the Gaussian, no Poisson-kernel pair, no
residue-calculus API — and the first of those is *still* true at 4.33.1.

None of it was relevant. The census listed the tools of the textbook residue proof and found them
missing; it did not ask whether a different proof needed them. This one needs only
`Complex.betaIntegral`, `Gamma_mul_Gamma_eq_betaIntegral`, `Gamma_mul_Gamma_one_sub` and a
one-dimensional change of variables, all of which predate the verdict. Same failure as the digamma
grep that searched for the *name* rather than the mathematics (see `Digamma.lean`): a gap stated in
terms of library availability answers the wrong question.

## What this does not give

`FirstMomentCore.lean`'s input 1 is the *inverse* direction,
`(1/2π)∫ P(λ) cos(λy) dλ = 1/(4cosh²(y/2))`. This file proves the forward transform. The inverse
follows by Fourier inversion (both sides are integrable and continuous), which is not done here.

No axiom, no `sorry`.
-/

open Real Complex MeasureTheory Set

noncomputable section

namespace GppLogisticFourierPair

/-- The logistic map `σ(x) = 1/(1+e^{-x})`, a smooth increasing bijection `ℝ → (0,1)`. -/
def logistic (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

lemma logistic_pos (x : ℝ) : 0 < logistic x := by unfold logistic; positivity

lemma one_sub_logistic (x : ℝ) :
    1 - logistic x = Real.exp (-x) / (1 + Real.exp (-x)) := by
  unfold logistic
  have : (1 + Real.exp (-x)) ≠ 0 := by positivity
  field_simp
  ring

lemma one_sub_logistic_pos (x : ℝ) : 0 < 1 - logistic x := by
  rw [one_sub_logistic]; positivity

/-- The density: `σ'(x) = e^{-x}/(1+e^{-x})²`. -/
def weight (x : ℝ) : ℝ := Real.exp (-x) / (1 + Real.exp (-x)) ^ 2

lemma weight_pos (x : ℝ) : 0 < weight x := by unfold weight; positivity

lemma hasDerivAt_logistic (x : ℝ) : HasDerivAt logistic (weight x) x := by
  have h1 : HasDerivAt (fun y => 1 + Real.exp (-y)) (-Real.exp (-x)) x := by
    have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_add 1
    simpa using this
  have hne : (1 + Real.exp (-x)) ≠ 0 := by positivity
  have h2 := h1.inv hne
  have e : weight x = - -Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 := by
    unfold weight; ring
  have hfun : logistic = (fun y => 1 + Real.exp (-y))⁻¹ := by
    funext y; simp [logistic, one_div, Pi.inv_apply]
  rw [e, hfun]
  exact h2

/-- The density is the logistic / Fermi–Dirac broadening kernel `1/(4cosh²(x/2))`. -/
lemma weight_eq_sech_sq (x : ℝ) : weight x = 1 / (4 * Real.cosh (x / 2) ^ 2) := by
  unfold weight
  rw [Real.cosh_eq]
  set a := Real.exp (x / 2) with ha_def
  set b := Real.exp (-(x / 2)) with hb_def
  have hab : a * b = 1 := by rw [ha_def, hb_def, ← Real.exp_add]; simp
  have hx : Real.exp (-x) = b ^ 2 := by
    rw [hb_def, sq, ← Real.exp_add]; congr 1; ring
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  rw [hx]
  have key : b * (a + b) = 1 + b ^ 2 := by nlinarith
  have h1 : (1 + b ^ 2) ≠ 0 := by positivity
  have h2 : (a + b) ≠ 0 := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have : (1 + b ^ 2) ^ 2 = (b * (a + b)) ^ 2 := by rw [key]
  nlinarith [this]

lemma logistic_strictMono : StrictMono logistic := by
  intro x y hxy
  unfold logistic
  have hx : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  apply one_div_lt_one_div_of_lt (by positivity)
  linarith

lemma logistic_image : logistic '' univ = Ioo (0 : ℝ) 1 := by
  ext u
  simp only [mem_image, mem_univ, true_and, mem_Ioo]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨logistic_pos x, by linarith [one_sub_logistic_pos x]⟩
  · rintro ⟨hu0, hu1⟩
    refine ⟨Real.log (u / (1 - u)), ?_⟩
    have h1u : 0 < 1 - u := by linarith
    have hq : 0 < u / (1 - u) := div_pos hu0 h1u
    unfold logistic
    rw [Real.exp_neg, Real.exp_log hq]
    field_simp
    ring

/-- The key pointwise identity: under `u = σ(x)`, the Beta kernel becomes a pure character. -/
lemma beta_kernel_logistic (t x : ℝ) :
    ((logistic x : ℝ) : ℂ) ^ ((t : ℂ) * I) * (1 - ((logistic x : ℝ) : ℂ)) ^ (-((t : ℂ) * I))
      = Complex.exp ((t : ℂ) * x * I) := by
  have hσ := logistic_pos x
  have h1σ := one_sub_logistic_pos x
  have hcast : (1 - ((logistic x : ℝ) : ℂ)) = (((1 - logistic x : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  rw [cpow_def_of_ne_zero (by exact_mod_cast hσ.ne'),
      cpow_def_of_ne_zero (by exact_mod_cast h1σ.ne'),
      ← ofReal_log hσ.le, ← ofReal_log h1σ.le, ← Complex.exp_add]
  congr 1
  have hlog : Real.log (logistic x) - Real.log (1 - logistic x) = x := by
    rw [← Real.log_div hσ.ne' h1σ.ne']
    have : logistic x / (1 - logistic x) = Real.exp x := by
      rw [one_sub_logistic]
      unfold logistic
      have hne : (1 + Real.exp (-x)) ≠ 0 := by positivity
      rw [Real.exp_neg]
      field_simp
    rw [this, Real.log_exp]
  have : ((Real.log (logistic x) : ℝ) : ℂ) - ((Real.log (1 - logistic x) : ℝ) : ℂ) = (x : ℂ) := by
    exact_mod_cast hlog
  linear_combination ((t : ℂ) * I) * this

/-- **Change of variables.** Under `u = σ(x)` the logistic Fourier integral is the Beta integral
`B(1+it, 1−it)`. This is the step that replaces the residue calculus the textbook proof uses. -/
theorem integral_weight_mul_exp_eq_betaIntegral (t : ℝ) :
    ∫ x : ℝ, ((weight x : ℝ) : ℂ) * Complex.exp ((t : ℂ) * x * I)
      = betaIntegral (1 + (t : ℂ) * I) (1 - (t : ℂ) * I) := by
  set G : ℝ → ℂ := fun u => ((u : ℂ)) ^ ((t : ℂ) * I) * (1 - (u : ℂ)) ^ (-((t : ℂ) * I))
    with hG
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := logistic)
    (f' := weight) MeasurableSet.univ (fun x _ => (hasDerivAt_logistic x).hasDerivWithinAt)
    logistic_strictMono.injective.injOn G
  rw [logistic_image, setIntegral_univ] at hcov
  have hrhs : (fun x => |weight x| • G (logistic x))
      = fun x => ((weight x : ℝ) : ℂ) * Complex.exp ((t : ℂ) * x * I) := by
    funext x
    rw [abs_of_pos (weight_pos x), hG]
    simp only
    rw [beta_kernel_logistic, Complex.real_smul]
  rw [hrhs] at hcov
  rw [← hcov]
  unfold betaIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have e1 : (1 + (t : ℂ) * I) - 1 = (t : ℂ) * I := by ring
  have e2 : (1 - (t : ℂ) * I) - 1 = -((t : ℂ) * I) := by ring
  rw [e1, e2]

lemma complex_Gamma_two : Complex.Gamma 2 = 1 := by
  have : (2 : ℂ) = 1 + 1 := by norm_num
  rw [this, Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, one_mul]

/-- The Beta integral at `(1+it, 1−it)` is `Γ(1+it)Γ(1−it)`, since `Γ(2) = 1`. -/
theorem betaIntegral_eq_gamma_mul (t : ℝ) :
    betaIntegral (1 + (t : ℂ) * I) (1 - (t : ℂ) * I)
      = Complex.Gamma (1 + (t : ℂ) * I) * Complex.Gamma (1 - (t : ℂ) * I) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := 1 + (t : ℂ) * I)
    (t := 1 - (t : ℂ) * I) (by simp) (by simp)
  have h2 : (1 + (t : ℂ) * I) + (1 - (t : ℂ) * I) = 2 := by ring
  rw [h2, complex_Gamma_two, one_mul] at h
  exact h.symm

/-- **The logistic Fourier pair.** For every real `t ≠ 0`,
`∫ℝ e^{itx} / (4 cosh²(x/2)) dx = πt / sinh(πt)`,
i.e. the celestial spectral weight `P(t)` is the Fourier transform of the logistic density.
Proved through the Beta integral and Euler reflection — no residue calculus, no `sech`
Fourier transform, and no Poisson kernel, none of which this proof uses. -/
theorem logistic_fourier_pair (t : ℝ) (ht : t ≠ 0) :
    ∫ x : ℝ, ((1 / (4 * Real.cosh (x / 2) ^ 2) : ℝ) : ℂ) * Complex.exp ((t : ℂ) * x * I)
      = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
  have hfun : (fun x : ℝ => ((1 / (4 * Real.cosh (x / 2) ^ 2) : ℝ) : ℂ)
        * Complex.exp ((t : ℂ) * x * I))
      = fun x => ((weight x : ℝ) : ℂ) * Complex.exp ((t : ℂ) * x * I) := by
    funext x; rw [weight_eq_sech_sq]
  rw [hfun, integral_weight_mul_exp_eq_betaIntegral, betaIntegral_eq_gamma_mul,
    GppGammaModulus.gamma_one_add_mul_gamma_one_sub t ht]

/-- At `t = 0` the pair reads `∫ 1/(4cosh²(x/2)) = 1`: the logistic density has total mass one,
matching `P(0) = 1`. -/
theorem integral_logistic_density :
    ∫ x : ℝ, ((1 / (4 * Real.cosh (x / 2) ^ 2) : ℝ) : ℂ) = 1 := by
  have hfun : (fun x : ℝ => ((1 / (4 * Real.cosh (x / 2) ^ 2) : ℝ) : ℂ))
      = fun x => ((weight x : ℝ) : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * x * I) := by
    funext x; rw [weight_eq_sech_sq]; simp
  rw [hfun, integral_weight_mul_exp_eq_betaIntegral, betaIntegral_eq_gamma_mul]
  simp [Complex.Gamma_one]

end GppLogisticFourierPair
