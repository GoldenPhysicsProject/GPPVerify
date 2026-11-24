/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import GppVerify.RiemannHypothesis.DigammaQuarterSech

/-!
# `ψ(1/4) = −γ − π/2 − 3 log 2`

Closed form of the digamma function at `1/4`, against Mathlib's `Complex.digamma = logDeriv Gamma`
and `Real.eulerMascheroniConstant`:

* `digamma_duplication_quarter`: `ψ(1/4) + ψ(3/4) = 2 ψ(1/2) − 2 log 2`, the logarithmic derivative
  of Legendre's duplication formula `Γ(s)Γ(s + ½) = Γ(2s) 2^{1−2s} √π` at `s = 1/4`;
* `digamma_reflection` (in this tree): `ψ(3/4) − ψ(1/4) = π cot(π/4) = π`;
* `digamma_one_half` (Mathlib): `ψ(1/2) = −γ − 2 log 2`.

Hence `ψ(1/4) = −γ − π/2 − 3 log 2` and `ψ(3/4) = −γ + π/2 − 3 log 2`.
No `sorry`, no `axiom`.
-/

namespace GppDigammaQuarter

open Complex
open scoped Real

private theorem ne_neg_nat_of_pos {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- Duplication for the digamma function at `1/4`. -/
theorem digamma_duplication_quarter :
    digamma (1 / 4) + digamma (3 / 4) = 2 * digamma (1 / 2) - 2 * Complex.log 2 := by
  have h14 : ∀ m : ℕ, ((1 / 4 : ℝ) : ℂ) ≠ -(m : ℂ) := ne_neg_nat_of_pos (by norm_num)
  have h34 : ∀ m : ℕ, ((3 / 4 : ℝ) : ℂ) ≠ -(m : ℂ) := ne_neg_nat_of_pos (by norm_num)
  have h12 : ∀ m : ℕ, ((1 / 2 : ℝ) : ℂ) ≠ -(m : ℂ) := ne_neg_nat_of_pos (by norm_num)
  have c14 : ((1 / 4 : ℝ) : ℂ) = 1 / 4 := by push_cast; ring
  have c34 : ((3 / 4 : ℝ) : ℂ) = 3 / 4 := by push_cast; ring
  have c12 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [c14] at h14; rw [c34] at h34; rw [c12] at h12
  set s : ℂ := 1 / 4 with hs
  have hs34 : s + 1 / 2 = 3 / 4 := by rw [hs]; ring
  have h2s : 2 * s = 1 / 2 := by rw [hs]; ring
  have g1 : Gamma s ≠ 0 := Gamma_ne_zero h14
  have g2 : Gamma (s + 1 / 2) ≠ 0 := by rw [hs34]; exact Gamma_ne_zero h34
  have g3 : Gamma (2 * s) ≠ 0 := by rw [h2s]; exact Gamma_ne_zero h12
  have hd1 : HasDerivAt Gamma (deriv Gamma s) s :=
    (differentiableAt_Gamma s h14).hasDerivAt
  have hd2 : HasDerivAt Gamma (deriv Gamma (s + 1 / 2)) (s + 1 / 2) :=
    (differentiableAt_Gamma (s + 1 / 2) (by rw [hs34]; exact h34)).hasDerivAt
  have hd3 : HasDerivAt Gamma (deriv Gamma (2 * s)) (2 * s) :=
    (differentiableAt_Gamma (2 * s) (by rw [h2s]; exact h12)).hasDerivAt
  -- left side
  have hL : HasDerivAt (fun w => Gamma w * Gamma (w + 1 / 2))
      (deriv Gamma s * Gamma (s + 1 / 2) + Gamma s * deriv Gamma (s + 1 / 2)) s := by
    exact hd1.mul (hd2.comp_add_const s (1 / 2))
  -- right side
  have hG2 : HasDerivAt (fun w => Gamma (2 * w)) (deriv Gamma (2 * s) * 2) s := by
    exact (hd3.comp s ((hasDerivAt_id s).const_mul (2 : ℂ))).congr_deriv (by ring)
  have hP : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w))
      ((2 : ℂ) ^ (1 - 2 * s) * Complex.log 2 * (-2)) s := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) s := by
      have := ((hasDerivAt_id s).const_mul (2 : ℂ)).const_sub 1
      simpa using this
    have := h1.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num))
    simpa using this
  have hR : HasDerivAt (fun w => Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((√π : ℝ) : ℂ))
      ((deriv Gamma (2 * s) * 2 * (2 : ℂ) ^ (1 - 2 * s)
        + Gamma (2 * s) * ((2 : ℂ) ^ (1 - 2 * s) * Complex.log 2 * (-2))) * ((√π : ℝ) : ℂ)) s := by
    have := (hG2.mul hP).mul_const ((√π : ℝ) : ℂ)
    exact this
  have hfun : (fun w => Gamma w * Gamma (w + 1 / 2))
      = fun w => Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((√π : ℝ) : ℂ) :=
    funext Complex.Gamma_mul_Gamma_add_half
  rw [hfun] at hL
  have huniq := hL.unique hR
  have hval := Complex.Gamma_mul_Gamma_add_half s
  have hp : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    exact Complex.exp_ne_zero _
  have hsq : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  -- translate to digamma
  have e1 : digamma s = deriv Gamma s / Gamma s := by
    rw [digamma_def, logDeriv_apply]
  have e2 : digamma (3 / 4) = deriv Gamma (s + 1 / 2) / Gamma (s + 1 / 2) := by
    rw [digamma_def, logDeriv_apply, hs34]
  have e3 : digamma (1 / 2) = deriv Gamma (2 * s) / Gamma (2 * s) := by
    rw [digamma_def, logDeriv_apply, h2s]
  rw [e2, e3]
  show digamma s + _ = _
  rw [e1]
  have key : ∀ A B A' B' : ℂ, A ≠ 0 → B ≠ 0 → A' / A + B' / B = (A' * B + A * B') / (A * B) := by
    intro A B A' B' hA hB
    field_simp
  rw [key _ _ _ _ g1 g2, huniq, hval]
  field_simp
  ring


/-- `ψ(3/4) − ψ(1/4) = π`. -/
theorem digamma_three_quarter_sub_quarter : digamma (3 / 4) - digamma (1 / 4) = π := by
  have h14 : ∀ m : ℕ, (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m
    have := ne_neg_nat_of_pos (x := 1 / 4) (by norm_num) m
    simpa using this
  have h34 : ∀ m : ℕ, 1 - (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m
    have := ne_neg_nat_of_pos (x := 3 / 4) (by norm_num) m
    have e : 1 - (1 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e]; exact this
  have hr := GppDigammaQuarterSech.digamma_reflection h14 h34
  have e1 : (1 : ℂ) - 1 / 4 = 3 / 4 := by norm_num
  rw [e1] at hr
  have hcs : cos ((π : ℂ) * (1 / 4)) / sin ((π : ℂ) * (1 / 4)) = 1 := by
    rw [show (π : ℂ) * (1 / 4) = ((π / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have : ((√2 / 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < √2 / 2 := by positivity
      exact_mod_cast this.ne'
    exact div_self this
  rw [hcs] at hr
  simpa using hr

/-- **`ψ(1/4) = −γ − π/2 − 3 log 2`.** -/
theorem digamma_quarter :
    digamma (1 / 4) = -(Real.eulerMascheroniConstant : ℂ) - (π : ℂ) / 2 - 3 * Complex.log 2 := by
  have h1 := digamma_duplication_quarter
  have h2 := digamma_three_quarter_sub_quarter
  have h3 := digamma_one_half
  rw [h3] at h1
  linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

/-- `ψ(3/4) = −γ + π/2 − 3 log 2`. -/
theorem digamma_three_quarter :
    digamma (3 / 4) = -(Real.eulerMascheroniConstant : ℂ) + (π : ℂ) / 2 - 3 * Complex.log 2 := by
  have h2 := digamma_three_quarter_sub_quarter
  have h4 := digamma_quarter
  linear_combination h2 + h4

/-- Real form: `ψ(1/4)` is the real number `−γ − π/2 − 3 log 2`. -/
theorem digamma_quarter_real :
    digamma (((1 / 4 : ℝ)) : ℂ) =
      ((-Real.eulerMascheroniConstant - π / 2 - 3 * Real.log 2 : ℝ) : ℂ) := by
  have : ((1 / 4 : ℝ) : ℂ) = 1 / 4 := by push_cast; ring
  rw [this, digamma_quarter]
  have hl : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ofNat, Complex.ofReal_log (by norm_num)]
  rw [hl]
  push_cast
  ring

end GppDigammaQuarter

#print axioms GppDigammaQuarter.digamma_duplication_quarter
#print axioms GppDigammaQuarter.digamma_quarter
#print axioms GppDigammaQuarter.digamma_three_quarter
#print axioms GppDigammaQuarter.digamma_quarter_real
