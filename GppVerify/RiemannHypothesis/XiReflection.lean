/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import GppVerify.RiemannHypothesis.XiZeroCounting
import GppVerify.RiemannHypothesis.XiLogDerivativeFormula
import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import GppVerify.RiemannHypothesis.MeyerSpectralWeil

/-!
# Explicit formula, stage E6c: reflection symmetry

* `logDeriv xi (1 - s) = - logDeriv xi s` (from `ξ(1 - s) = ξ(s)`).
* `Φ_g(1 - s) = Φ_{g(-·)}(s)` for the spectral transform `Φ_g(s) = ∫ g(u) e^{(s - 1/2) u} du`.
* The reflected function `g(-·)` is again a test function.

These turn the left vertical line of the contour into a right-line integral against `Φ(s) + Φ(1 - s)`.
-/

open Complex MeasureTheory GppMeyerSpectralWeil
open scoped ContDiff

namespace GppXiReflection

open GppLogDerivZeroFree

/-- The logarithmic derivative of `ξ` is odd under `s ↦ 1 - s`. -/
theorem logDeriv_xi_one_sub (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h2 : HasDerivAt xi (deriv xi (1 - s)) (1 - s) := (differentiable_xi (1 - s)).hasDerivAt
  have hd : HasDerivAt (fun w : ℂ => xi (1 - w)) (deriv xi (1 - s) * -1) s :=
    HasDerivAt.comp (h₂ := xi) s h2 h1
  have hd' : HasDerivAt xi (deriv xi (1 - s) * -1) s :=
    hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => (xi_one_sub w).symm)
  have hd2 : deriv xi s = -deriv xi (1 - s) := by rw [hd'.deriv]; ring
  rw [logDeriv_apply, logDeriv_apply, hd2, xi_one_sub]
  ring

/-- Reflection of the test function. -/
theorem isTestFunction_neg {g : ℝ → ℝ} (hg : IsTestFunction g) : IsTestFunction (fun u => g (-u)) :=
  ⟨hg.1.comp contDiff_neg, by convert hg.2.comp_homeomorph (Homeomorph.neg ℝ) using 1; rfl⟩

/-- `Φ_g(1 - s) = Φ_{g(-·)}(s)`. -/
theorem spectralTransform_one_sub (g : ℝ → ℝ) (s : ℂ) :
    spectralTransform g (1 - s) = spectralTransform (fun u => g (-u)) s := by
  unfold spectralTransform
  rw [← integral_neg_eq_self (fun u : ℝ => (g u : ℂ) * Complex.exp ((1 - s - 1 / 2) * u))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.ofReal_neg]
  congr 2
  ring

/-- `ξ` has no zeros in `Re s ≥ 1`. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1
    unfold xi
    simp
  · have hre : 0 < s.re := by linarith
    have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hre
    rw [GppXiZeroCounting.xi_eq_mul hre hs1]
    refine mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
      two_ne_zero) (Gammaℝ_ne_zero_of_re_pos hre)) (riemannZeta_ne_zero_of_one_le_re h)

/-- `ξ` has no zeros in `Re s ≤ 0`. -/
theorem xi_ne_zero_of_re_le_zero {s : ℂ} (h : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_one_sub]
  exact xi_ne_zero_of_one_le_re (by simp; linarith)

/-- Every zero of `ξ` lies in the open critical strip. -/
theorem xi_zero_mem_strip {s : ℂ} (h : xi s = 0) : 0 < s.re ∧ s.re < 1 := by
  by_contra hcon
  rcases not_and_or.1 hcon with h1 | h1
  · exact xi_ne_zero_of_re_le_zero (not_lt.1 h1) h
  · exact xi_ne_zero_of_one_le_re (not_lt.1 h1) h

/-- Zeros of `ξ` are exactly the nontrivial zeros of `ζ`. -/
theorem xi_eq_zero_iff_nontrivial (s : ℂ) :
    xi s = 0 ↔ s ∈ GppWeilCriterion.nontrivialZeros := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := xi_zero_mem_strip h
    have hs1 : s ≠ 1 := fun e => by simp [e] at h1
    have hs0 : s ≠ 0 := fun e => by simp [e] at h0
    rw [GppXiZeroCounting.xi_eq_mul h0 hs1] at h
    have hz : riemannZeta s = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exfalso
        rcases mul_eq_zero.1 h' with h'' | h''
        · rcases div_eq_zero_iff.1 h'' with h3 | h3
          · rcases mul_eq_zero.1 h3 with h4 | h4
            · exact hs0 h4
            · exact hs1 (sub_eq_zero.1 h4)
          · exact two_ne_zero h3
        · exact Gammaℝ_ne_zero_of_re_pos h0 h''
      · exact h'
    exact ⟨hz, h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    have hs1 : s ≠ 1 := fun e => by simp [e] at h1
    have hs0 : s ≠ 0 := fun e => by simp [e] at h0
    exact xi_eq_zero_of_zeta_zero hz hs0 hs1 (Gammaℝ_ne_zero_of_re_pos h0)

end GppXiReflection
