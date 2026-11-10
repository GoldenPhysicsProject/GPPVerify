/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import GppVerify.RiemannHypothesis.SpectralInversion

/-!
# Explicit formula, stage E6b: the prime terms on the line `Re s = 2`

For a test function `g` and `Φ(s) = ∫ g(u) e^{(s - 1/2) u} du`,

  `(1/2π) ∫ (-ζ'/ζ)(2 + i t) Φ(2 + i t) dt = ∑ₙ Λ(n) g(log n) / √n`.

Each Dirichlet term `Λ(n) n^{-(2 + i t)}` integrates against `Φ(2 + i t)` to `Λ(n) n^{-1/2} g(log n)` by
Fourier inversion (`GppSpectralInversion.line_inversion` with `σ = 2`, `v = log n`), and the sum may be
exchanged with the integral because `∑ Λ(n) n^{-2} < ∞` and `Φ(2 + i ·)` is integrable.
-/

open Complex Set MeasureTheory FourierTransform SchwartzMap GppMeyerSpectralWeil
open GppExplicitFormulaE1 GppSpectralInversion
open scoped ArithmeticFunction.vonMangoldt

namespace GppPrimeLine

/-- `t ↦ Φ(σ + i t)` is integrable. -/
theorem line_integrable {g : ℝ → ℝ} (hg : IsTestFunction g) (σ : ℝ) : Integrable (line g σ) := by
  have h : line g σ = fun t => (𝓕 (shiftedSchwartz hg σ)) (-t / (2 * Real.pi)) :=
    funext (line_eq_fourier hg σ)
  rw [h]
  have hI : Integrable (fun x => (𝓕 (shiftedSchwartz hg σ)) x) volume :=
    (𝓕 (shiftedSchwartz hg σ)).integrable
  have := hI.comp_mul_left' (R := -(2 * Real.pi)⁻¹) (by simp [Real.pi_ne_zero])
  refine this.congr (Filter.Eventually.of_forall fun r => ?_)
  show (𝓕 (shiftedSchwartz hg σ)) (-(2 * Real.pi)⁻¹ * r) = _
  congr 1
  field_simp

theorem line_continuous {g : ℝ → ℝ} (hg : IsTestFunction g) (σ : ℝ) : Continuous (line g σ) := by
  have h : line g σ = fun t => (𝓕 (shiftedSchwartz hg σ)) (-t / (2 * Real.pi)) :=
    funext (line_eq_fourier hg σ)
  rw [h]
  exact (𝓕 (shiftedSchwartz hg σ)).continuous.comp (by fun_prop)

/-- For `n ≥ 1`, `n^{-s} = e^{-2 log n} · e^{-i t log n}` on `s = 2 + i t`. -/
theorem natCast_cpow_line {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-((2 : ℝ) + t * Complex.I : ℂ)) =
      Complex.exp (-2 * (Real.log n : ℂ)) * Complex.exp (-(Complex.I * t * (Real.log n : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add]
  congr 1
  have : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [this]
  push_cast
  ring

theorem exp_mul_exp_sqrt {n : ℕ} (hn : 1 ≤ n) :
    Complex.exp (-2 * (Real.log n : ℂ)) * Complex.exp ((((2 : ℝ) : ℂ) - 1 / 2) * (Real.log n : ℂ)) =
      ((Real.sqrt n)⁻¹ : ℝ) := by
  rw [← Complex.exp_add]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have : Complex.exp (-2 * (Real.log n : ℂ) + (((2 : ℝ) : ℂ) - 1 / 2) * (Real.log n : ℂ)) =
      ((Real.exp (-(1 / 2) * Real.log n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [this]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, ← Real.exp_neg]
  congr 1
  ring

/-- **One prime term.** -/
theorem term_integral {g : ℝ → ℝ} (hg : IsTestFunction g) {n : ℕ} (hn : 1 ≤ n) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((2 : ℝ) + t * Complex.I : ℂ) n * line g 2 t =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (g (Real.log n) : ℂ) / (Real.sqrt n : ℂ) := by
  have hv0 : (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) 0 = 0 := by simp
  have hterm : ∀ t : ℝ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((2 : ℝ) + t * Complex.I : ℂ) n * line g 2 t =
      ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-2 * (Real.log n : ℂ))) *
        (Complex.exp (-(Complex.I * t * (Real.log n : ℂ))) * line g 2 t) := by
    intro t
    rw [LSeries.term_def₀ hv0, natCast_cpow_line hn t]
    ring
  simp_rw [hterm]
  rw [integral_const_mul]
  have hinv := line_inversion hg 2 (Real.log n)
  have hsq : (Real.sqrt n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have key := exp_mul_exp_sqrt hn
  generalize (∫ t : ℝ, Complex.exp (-(Complex.I * t * (Real.log n : ℂ))) * line g 2 t) = J at hinv ⊢
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hJ : J = ((2 * Real.pi : ℝ) : ℂ) * ((g (Real.log n) : ℂ) *
      Complex.exp ((((2 : ℝ) : ℂ) - 1 / 2) * (Real.log n : ℂ))) := by
    rw [hinv]; push_cast; field_simp
  rw [hJ]
  have : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]; field_simp; simp
  calc ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-2 * (Real.log n : ℂ)) * (((2 * Real.pi : ℝ) : ℂ) * ((g (Real.log n) : ℂ) *
          Complex.exp ((((2 : ℝ) : ℂ) - 1 / 2) * (Real.log n : ℂ)))))
      = (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
          (g (Real.log n) : ℂ) * (Complex.exp (-2 * (Real.log n : ℂ)) *
            Complex.exp ((((2 : ℝ) : ℂ) - 1 / 2) * (Real.log n : ℂ)))) := by ring
    _ = _ := by
      rw [this, key, one_mul]
      push_cast
      field_simp

end GppPrimeLine
