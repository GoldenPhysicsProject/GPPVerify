/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import GppVerify.RiemannHypothesis.XiZeroCounting

/-!
# Explicit formula, stage E6a: the logarithmic derivative of `ξ`

For `Re s > 0`, `s ≠ 1` and `ξ s ≠ 0`,

  `ξ'/ξ (s) = 1/s + 1/(s - 1) - (log π)/2 + ψ(s/2)/2 + ζ'/ζ (s)`,

where `ψ = Γ'/Γ` is Mathlib's `Complex.digamma`. This is the splitting of the integrand of the
contour integral into the pole term, the Archimedean term and the prime term.
-/

open Complex

namespace GppXiZeroCounting

open GppLogDerivZeroFree

/-- The logarithmic derivative of the Archimedean factor `Γℝ`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2 := by
  have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hG : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hpole
  have hGne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact this.const_cpow (Or.inl hpi)
  have h2 : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    have hd : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact HasDerivAt.comp (h₂ := Complex.Gamma) s hG.hasDerivAt hd
  have hpne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    tauto
  have hGam : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := rfl
  rw [hGam, logDeriv_mul s hpne hGne h1.differentiableAt h2.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, h1.deriv, h2.deriv]
  rw [digamma_def, logDeriv_apply]
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_pos.le]
  rw [hlog]
  field_simp

/-- `ξ(w) = w (w - 1) / 2 · Γℝ(w) · ζ(w)` for `Re w > 0`, `w ≠ 1`. -/
theorem xi_eq_mul {w : ℂ} (hre : 0 < w.re) (hw1 : w ≠ 1) :
    xi w = w * (w - 1) / 2 * Gammaℝ w * riemannZeta w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hre
  have hg : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hz : riemannZeta w = completedRiemannZeta w / Gammaℝ w := riemannZeta_def_of_ne_zero hw0
  have hL : completedRiemannZeta w = completedRiemannZeta₀ w - 1 / w - 1 / (1 - w) := by
    have := completedRiemannZeta_eq w
    linear_combination this
  have h1w : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  rw [hz, hL]
  unfold xi
  field_simp
  ring

/-- **E6a: the logarithmic derivative of `ξ`.** For `Re s > 0`, `s ≠ 1`, `ξ s ≠ 0`,
`ξ'/ξ (s) = 1/s + 1/(s-1) - (log π)/2 + ψ(s/2)/2 + ζ'/ζ (s)`. -/
theorem logDeriv_xi_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) (hxi : xi s ≠ 0) :
    logDeriv xi s = 1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2) +
      logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hre
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGd : DifferentiableAt ℂ Gammaℝ s := by
    have hGam : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := rfl
    rw [hGam]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s :=
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s :=
      (Complex.differentiableAt_Gamma _ hpole).comp s (by fun_prop)
    exact h1.mul h2
  have hGne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hzd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hev : xi =ᶠ[nhds s] fun w => (w * (w - 1) / 2 * Gammaℝ w) * riemannZeta w := by
    filter_upwards [(continuous_re.continuousAt.eventually (lt_mem_nhds hre)),
      (continuousAt_id.eventually_ne hs1)] with w hw hw1
    exact xi_eq_mul hw hw1
  have hzne : riemannZeta s ≠ 0 := by
    intro h
    apply hxi
    rw [xi_eq_mul hre hs1, h, mul_zero]
  have hP : (s * (s - 1) / 2) ≠ 0 := div_ne_zero (mul_ne_zero hs0 hs1') two_ne_zero
  have hPd : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((s - 1 + s) / 2) s := by
    have := (((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2)
    simpa using this
  have hlogP : logDeriv (fun w : ℂ => w * (w - 1) / 2) s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_apply, hPd.deriv]
    field_simp
  have hlog1 : logDeriv xi s =
      logDeriv (fun w => (w * (w - 1) / 2 * Gammaℝ w) * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlog1, logDeriv_mul (f := fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) (g := riemannZeta) s
      (mul_ne_zero hP hGne) hzne (hPd.differentiableAt.mul hGd) hzd,
    logDeriv_mul (f := fun w : ℂ => w * (w - 1) / 2) (g := Gammaℝ) s hP hGne
      hPd.differentiableAt hGd, hlogP, logDeriv_Gammaℝ hre]

end GppXiZeroCounting
