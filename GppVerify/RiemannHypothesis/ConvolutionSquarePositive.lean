import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# Convolution squares are positive-type — the gap of PR #45, closed

Thread B of `docs/FORMALIZATION_PLAN.md`. `HaarPositivityWeil.lean` (PR #45) honestly
stubbed the central claim of `haar_positivity_weil_wightman.tex` — *the convolution square
of a function on a group is positive-type* — naming its exact gap: integrability of the
pairwise-translated products `f(·+a)·f(·+b)`, needed for the sum–integral interchange.

This file closes that gap for `ℝ` with Lebesgue measure (THE Haar measure on `ℝ`), for
integrable **bounded** `f`, exactly the hypothesis set the stub proposed:

* the products are integrable (`Integrable.comp_add_right` for the translation,
  `Integrable.bdd_mul` for the bounded factor);
* `P(a−b) = ∫ f(y+a)·f(y+b) dy` (right-translation invariance,
  `integral_add_right_eq_self`);
* the finite sum interchanges with the integral (`integral_finset_sum`), and the
  pointwise sum is `‖Σᵢ cᵢ·f(y+xᵢ)‖² ≥ 0` — the same Gram-square identity as
  `YakaboyluPositivityKernel.lean`, now under an integral sign.

`GppHaarPositivityWeil.PositiveType` is reused unchanged, so this theorem plugs directly
into that file's framework (Weil/Wightman/OS positivity as instances of one construction).
The idèle-class-group version remains open for the honest reason recorded there: idèle
class groups are not in Mathlib.
-/

namespace GppHaarPositivityWeil

open MeasureTheory Finset

/-- The pairwise-translated product is integrable: the exact integrability fact whose
    absence was the documented gap. -/
theorem integrable_shift_mul_shift {f : ℝ → ℝ} (hf : Integrable f (volume : Measure ℝ))
    {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) (a b : ℝ) :
    Integrable (fun y => f (y + a) * f (y + b)) (volume : Measure ℝ) := by
  have ha : Integrable (fun y => f (y + a)) (volume : Measure ℝ) := hf.comp_add_right a
  have hb : Integrable (fun y => f (y + b)) (volume : Measure ℝ) := hf.comp_add_right b
  exact hb.bdd_mul (c := C) ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbdd (y + a))

/-- Translation identity: `P(a−b) = ∫ f(y+a)·f(y+b) dy`, by right-invariance of Lebesgue
    measure. -/
theorem convolution_shift {f : ℝ → ℝ} (a b : ℝ) :
    (∫ y, f y * f (y - (a - b))) = ∫ y, f (y + a) * f (y + b) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => f y * f (y - (a - b))) a
  have harg : ∀ y : ℝ, y + a - (a - b) = y + b := fun y => by ring
  simp only [harg] at h
  exact h.symm

/-- `(z·↑r).re = z.re·r` — the specialized form whose rewrite pattern requires the second
    factor to be a real coercion, so it can never grab a plain complex product elsewhere
    in the goal (the general `Complex.mul_re` does, by traversal order). -/
theorem mul_ofReal_re (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The pointwise Gram-square identity: for real amplitudes `aᵢ`,
    `Σᵢⱼ Re(c̄ᵢcⱼ)·aᵢ·aⱼ = normSq(Σᵢ cᵢ·aᵢ) ≥ 0`. -/
theorem gram_square_nonneg {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * (a i * a j) := by
  have hkey : ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * (a i * a j) =
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i * (a i : ℂ)) * (c j * (a j : ℂ))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hexpand : (starRingEnd ℂ) (c i * (a i : ℂ)) * (c j * (a j : ℂ)) =
        (starRingEnd ℂ) (c i) * c j * ((a i * a j : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hexpand, mul_ofReal_re]
  rw [hkey]
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (starRingEnd ℂ) (c i * (a i : ℂ)) * (c j * (a j : ℂ)) =
      (starRingEnd ℂ) (∑ i : Fin n, c i * (a i : ℂ)) *
        (∑ i : Fin n, c i * (a i : ℂ)) := by
    rw [map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hsum, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **Convolution squares are positive-type** (the stubbed claim of
    `haar_positivity_weil_wightman.tex`, now a theorem): for integrable bounded
    `f : ℝ → ℝ`, the function `P(x) = ∫ f(y)·f(y−x) dy` is positive-type. -/
theorem convolution_square_positive_type {f : ℝ → ℝ}
    (hf : Integrable f (volume : Measure ℝ)) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    PositiveType (fun x => ∫ y, f y * f (y - x)) := by
  intro n x c
  -- Step 1: rewrite each matrix entry through the translation identity.
  have hentry : ∀ i j : Fin n,
      ((fun x => ∫ y, f y * f (y - x)) (x i - x j) : ℂ) =
        ((∫ y, f (y + x i) * f (y + x j) : ℝ) : ℂ) := by
    intro i j
    norm_cast
    exact convolution_shift (x i) (x j)
  simp only [hentry]
  -- Step 2: push `.re` through the double sum and strip the real coercion.
  rw [Complex.re_sum]
  have hterm : ∀ i : Fin n,
      (∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        ((∫ y, f (y + x i) * f (y + x j) : ℝ) : ℂ)).re =
      ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
        ∫ y, f (y + x i) * f (y + x j) := by
    intro i
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_ofReal_re]
  simp only [hterm]
  -- Step 3: interchange the finite double sum with the integral.
  have hint : ∀ i j : Fin n,
      Integrable (fun y => ((starRingEnd ℂ) (c i) * c j).re *
        (f (y + x i) * f (y + x j))) (volume : Measure ℝ) :=
    fun i j => (integrable_shift_mul_shift hf hbdd (x i) (x j)).const_mul _
  have hswap : ∑ i : Fin n, ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
      ∫ y, f (y + x i) * f (y + x j) =
      ∫ y, ∑ i : Fin n, ∑ j : Fin n,
        ((starRingEnd ℂ) (c i) * c j).re * (f (y + x i) * f (y + x j)) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
      · exact fun j _ => hint i j
    · exact fun i _ => integrable_finset_sum _ fun j _ => hint i j
  rw [hswap]
  -- Step 4: the integrand is a Gram square, hence nonnegative pointwise.
  apply integral_nonneg
  intro y
  exact gram_square_nonneg c fun i => f (y + x i)

end GppHaarPositivityWeil
