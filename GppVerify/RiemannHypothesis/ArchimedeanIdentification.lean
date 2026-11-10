/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.RiemannHypothesis.DigammaIntegral
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Decay
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity

/-!
# Explicit formula, stage E6 (Archimedean term), part 2: the identification

For an even test function `g` with `h(r) = ĝ(1/2 + i r) = ∫ g(u) e^{i r u} du`,

  `archimedeanTerm g = -g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr`.

Proof: Gauss's integral for `ψ` (part 1), Fubini in `(r, t)`, and Fourier inversion
`(1/2π) ∫ h(r) cos(r v) dr = g(v)`.
-/

open Complex Set MeasureTheory

namespace GppArchimedeanId

/-- The kernel of Gauss's integral at `z`. -/
noncomputable def K (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)) / (1 - Complex.exp (-(t : ℂ)))

/-- For `z = 1/4 + i r/2` the kernel is bounded by `(4 + |r|) e^{1/4} e^{-t/4}`, uniformly in `t > 0`. -/
theorem norm_K_le (r : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t‖ ≤ (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) := by
  set z : ℂ := (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I with hz
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hznorm : ‖z‖ ≤ 1 / 4 + |r| / 2 := by
    calc ‖z‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖((r / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 / 4 + |r| / 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
        simp
  have hden : 0 < 1 - Real.exp (-t) := by
    have := Real.exp_lt_exp.2 (by linarith : -t < 0)
    rw [Real.exp_zero] at this
    linarith
  have hdenC : ‖1 - Complex.exp (-(t : ℂ))‖ = 1 - Real.exp (-t) := by
    have : (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [this, Complex.norm_real, Real.norm_of_nonneg hden.le]
  have hbase : 1 ≤ Real.exp (1 / 4) * Real.exp (-t / 4) ∨ 1 ≤ t := by
    by_cases h1 : t < 1
    · left
      rw [← Real.exp_add]
      apply Real.one_le_exp
      linarith
    · right; linarith
  unfold K
  rw [norm_div, hdenC]
  rcases le_or_gt 1 t with h1 | h1
  · -- large t
    have hnum : ‖Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)‖ ≤ 2 * Real.exp (-t / 4) := by
      refine (norm_sub_le _ _).trans ?_
      have e1 : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
        rw [Complex.norm_exp]; simp
      have e2 : ‖Complex.exp (-z * t)‖ = Real.exp (-t / 4) := by
        rw [Complex.norm_exp]
        congr 1
        simp [hzre]
        ring
      rw [e1, e2]
      have : Real.exp (-t) ≤ Real.exp (-t / 4) := Real.exp_le_exp.2 (by linarith)
      linarith
    have hd2 : 1 / 2 ≤ 1 - Real.exp (-t) := by
      have h2 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      linarith
    rw [div_le_iff₀ hden]
    have he : 1 ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
    have hr : 0 ≤ |r| := abs_nonneg r
    have hep : 0 < Real.exp (-t / 4) := Real.exp_pos _
    have hA : 4 ≤ (4 + |r|) * Real.exp (1 / 4) := by nlinarith
    have h5 : 4 * Real.exp (-t / 4) * (1 / 2) ≤
        (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) * (1 - Real.exp (-t)) := by
      have h6 : 4 * Real.exp (-t / 4) ≤ (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) :=
        mul_le_mul_of_nonneg_right hA hep.le
      calc 4 * Real.exp (-t / 4) * (1 / 2) ≤
          (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) * (1 / 2) := by gcongr
        _ ≤ _ := by gcongr
    linarith
  · -- small t
    have hnum : ‖Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)‖ ≤
        ‖z‖ * t + (1 - Real.exp (-t)) := by
      have e : Complex.exp (-(t : ℂ)) - Complex.exp (-z * t) =
          (1 - Complex.exp (-z * t)) - (1 - Complex.exp (-(t : ℂ))) := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have h2 : ‖1 - Complex.exp (-z * t)‖ ≤ ‖z‖ * t := by
        have := GppDigammaIntegral.norm_one_sub_exp_neg_le (w := z * t) (by simpa [hzre] using by positivity)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
        simpa [neg_mul] using this
      rw [hdenC]
      linarith
    have hd2 : t / 2 ≤ 1 - Real.exp (-t) := by
      have h3 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      have h4 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
      have h5 : Real.exp (-t) ≤ 1 - t / 2 := by
        rw [h4]
        have h6 : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := inv_anti₀ (by positivity) h3
        have h7 : (1 + t)⁻¹ ≤ 1 - t / 2 := by
          rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      linarith
    rw [div_le_iff₀ hden]
    have hAE : 1 ≤ Real.exp (1 / 4) * Real.exp (-t / 4) := by
      rcases hbase with h | h
      · exact h
      · linarith
    have hr : 0 ≤ |r| := abs_nonneg r
    have hD : 0 < 1 - Real.exp (-t) := hden
    have h8 : ‖z‖ * t ≤ (1 / 2 + |r|) * (1 - Real.exp (-t)) := by
      have : t ≤ 2 * (1 - Real.exp (-t)) := by linarith
      calc ‖z‖ * t ≤ ‖z‖ * (2 * (1 - Real.exp (-t))) := by gcongr
        _ ≤ (2 * (1 / 4 + |r| / 2)) * (1 - Real.exp (-t)) := by nlinarith [norm_nonneg z]
        _ = (1 / 2 + |r|) * (1 - Real.exp (-t)) := by ring
    have h9 : (4 + |r|) * 1 * (1 - Real.exp (-t)) ≤
        (4 + |r|) * (Real.exp (1 / 4) * Real.exp (-t / 4)) * (1 - Real.exp (-t)) := by
      gcongr
    nlinarith

end GppArchimedeanId
