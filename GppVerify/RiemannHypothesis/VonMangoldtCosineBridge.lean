import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-!
# Von Mangoldt cosine bridge

This file simplifies the real part of each absolutely-convergent von-Mangoldt
L-series term on `s = a + i t` to the expected exponential-decay cosine kernel.
It also records the exact finite positive-type layer: each arithmetic cosine mode
is positive type and therefore every finite collection of modes is positive type.
The infinite `tsum` passage is deliberately kept separate.
-/

namespace GppVonMangoldtCosine

open Complex LSeries
open ArithmeticFunction
open GppGlobalVonMangoldt
open GppHaarPositivityWeil

/-- Real part of the negative complex power of a positive integer base. -/
theorem natCast_neg_cpow_re
    (n : ℕ) (hn : n ≠ 0) (a t : ℝ) :
    (((n : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I))).re) =
      Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
    Complex.natCast_log.symm
  rw [hlog, Complex.exp_re]
  have hre :
      (((Real.log n : ℂ) * -((a : ℂ) + (t : ℂ) * Complex.I)).re) =
        -Real.log n * a := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.add_re, Complex.I_re, mul_zero, add_zero,
      zero_mul, sub_zero]
    ring
  have him :
      (((Real.log n : ℂ) * -((a : ℂ) + (t : ℂ) * Complex.I)).im) =
        -Real.log n * t := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero,
      mul_one, sub_zero]
    ring
  rw [hre, him]
  rw [show -Real.log n * t = -(Real.log n * t) by ring, Real.cos_neg]

/-- Each nonzero-index von-Mangoldt term has the expected cosine real part. -/
theorem vonMangoldt_term_re_eq_exp_cos
    (n : ℕ) (hn : n ≠ 0) (a t : ℝ) :
    (LSeries.term vonMangoldtComplex
      ((a : ℂ) + (t : ℂ) * Complex.I) n).re =
      ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  rw [LSeries.term_of_ne_zero hn]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  change
    (((ArithmeticFunction.vonMangoldt n : ℂ) *
      ((n : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I)))).re) =
      ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t)
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [natCast_neg_cpow_re n hn a t]
  ring

/-- The zero-index term vanishes. -/
theorem vonMangoldt_term_zero_re (a t : ℝ) :
    (LSeries.term vonMangoldtComplex
      ((a : ℂ) + (t : ℂ) * Complex.I) 0).re = 0 := by
  simp

/-- Global von-Mangoldt cosine series on the half-plane of absolute convergence. -/
theorem neg_zeta_logDeriv_re_eq_vonMangoldt_cosine_tsum
    {a t : ℝ} (ha : 1 < a) :
    (-(deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I) /
      riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  have hs : 1 < (((a : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using ha
  rw [neg_zeta_logDeriv_re_eq_tsum_re_terms hs]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact vonMangoldt_term_re_eq_exp_cos n hn a t

/-- A pure cosine frequency is positive type.  Its Gram matrix splits into the sum
of the cosine and sine Gram squares by `cos(A-B)`. -/
theorem cosine_frequency_positiveType (freq : ℝ) :
    PositiveType (fun t : ℝ => Real.cos (freq * t)) := by
  intro n x c
  rw [Complex.re_sum]
  have hterm : ∀ i : Fin n,
      (∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        ((Real.cos (freq * (x i - x j)) : ℝ) : ℂ)).re =
      ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
        Real.cos (freq * (x i - x j)) := by
    intro i
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_ofReal_re]
  simp only [hterm]
  have hsplit : ∀ i j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * Real.cos (freq * (x i - x j)) =
        ((starRingEnd ℂ) (c i) * c j).re *
          (Real.cos (freq * x i) * Real.cos (freq * x j)) +
        ((starRingEnd ℂ) (c i) * c j).re *
          (Real.sin (freq * x i) * Real.sin (freq * x j)) := by
    intro i j
    rw [mul_sub, Real.cos_sub]
    ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  exact add_nonneg
    (gram_square_nonneg c (fun i => Real.cos (freq * x i)))
    (gram_square_nonneg c (fun i => Real.sin (freq * x i)))

/-- Positive type is preserved by multiplication by a nonnegative real scalar. -/
theorem positiveType_nonneg_scalar {f : ℝ → ℝ}
    (hf : PositiveType f) {r : ℝ} (hr : 0 ≤ r) :
    PositiveType (fun t => r * f t) := by
  intro n x c
  have h := hf n x c
  let S : ℂ := ∑ i : Fin n, ∑ j : Fin n,
    (starRingEnd ℂ (c i)) * c j * (f (x i - x j) : ℂ)
  have hS : 0 ≤ S.re := by
    simpa [S] using h
  have heq :
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (c i)) * c j * (((r * f (x i - x j)) : ℝ) : ℂ)) =
      (r : ℂ) * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  rw [heq]
  simpa [Complex.mul_re] using mul_nonneg hr hS

/-- Every individual von-Mangoldt cosine mode is positive type, for every real radial
parameter `a`.  No convergence or critical-strip statement is involved here. -/
theorem vonMangoldt_mode_positiveType (a : ℝ) (n : ℕ) :
    PositiveType (fun t : ℝ =>
      ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n * a) *
        Real.cos (Real.log n * t)) := by
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n * a) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  simpa [mul_assoc] using
    positiveType_nonneg_scalar (cosine_frequency_positiveType (Real.log n)) hc

/-- Finite sums preserve positive type. -/
theorem positiveType_finset_sum_modes
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, PositiveType (f i)) :
    PositiveType (fun t => ∑ i in S, f i t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro n x c
      simp
  | @insert a S ha ih =>
      have haPT : PositiveType (f a) := hf a (by simp)
      have hSPT : PositiveType (fun t => ∑ i in S, f i t) := by
        apply ih
        intro i hi
        exact hf i (by simp [hi])
      intro n x c
      have h1 := haPT n x c
      have h2 := hSPT n x c
      simpa [ha, Finset.sum_add_distrib, add_mul, mul_add] using add_nonneg h1 h2

/-- Every finite truncation of the global von-Mangoldt cosine response is positive type. -/
theorem finite_vonMangoldt_cosine_positiveType (a : ℝ) (S : Finset ℕ) :
    PositiveType (fun t : ℝ =>
      ∑ n in S, ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n * a) *
        Real.cos (Real.log n * t)) := by
  apply positiveType_finset_sum_modes S
  intro n hn
  exact vonMangoldt_mode_positiveType a n

end GppVonMangoldtCosine

#print axioms GppVonMangoldtCosine.natCast_neg_cpow_re
#print axioms GppVonMangoldtCosine.vonMangoldt_term_re_eq_exp_cos
#print axioms GppVonMangoldtCosine.neg_zeta_logDeriv_re_eq_vonMangoldt_cosine_tsum
#print axioms GppVonMangoldtCosine.cosine_frequency_positiveType
#print axioms GppVonMangoldtCosine.vonMangoldt_mode_positiveType
#print axioms GppVonMangoldtCosine.finite_vonMangoldt_cosine_positiveType
