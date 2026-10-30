import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Convolution squares are positive-type on any abelian group with an invariant measure

Source: `haar_positivity_weil_wightman.tex`, thm:haar-square-positive. Daniel Toupin / Golden
Physics Project, with AI assistance from Claude Code.

`ConvolutionSquarePositive.lean` proves this for `ℝ` with Lebesgue measure. The argument uses
only translation invariance of the measure, so it holds for every additive commutative group `G`
carrying a right-invariant measure `μ` (in particular, a Haar measure on a locally compact abelian
group). This file states it at that generality.

* `convolution_shift_group`: `∫ f(y) f(y − (a − b)) dμ = ∫ f(y + a) f(y + b) dμ`.
* `GroupPositiveType P`: for every finite family of points `xᵢ` and complex weights `cᵢ`,
  `0 ≤ Σᵢⱼ c̄ᵢ cⱼ P(xᵢ − xⱼ)` as a complex number (so the sum is real and nonnegative).
* `convolution_square_positive_type_group`: for integrable bounded real `f`, the convolution
  square `P(x) = ∫ f(y) f(y − x) dμ` is of positive type.

**Scope.** This is the abstract statement only. Instantiating it to the idèle class group `C_k`
needs `C_k` as a topological abelian group with a Haar measure, which Mathlib does not provide, so
`open_adelic_haar_square_positive_type` stays a stub. Positivity of a Haar square is unconditional
and is *not* Weil positivity, which concerns the specific distribution `D_k`; see
`NoGo/HaarSquareNotReflection.lean`. No claim about RH.
-/

set_option autoImplicit false

open MeasureTheory Finset
open scoped ComplexOrder

namespace GppConvolutionSquareGroup

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
  {μ : Measure G} [μ.IsAddRightInvariant]

/-- The pairwise-translated product is integrable. -/
theorem integrable_shift_mul_shift_group {f : G → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) (a b : G) :
    Integrable (fun y => f (y + a) * f (y + b)) μ := by
  have ha : Integrable (fun y => f (y + a)) μ := hf.comp_add_right a
  have hb : Integrable (fun y => f (y + b)) μ := hf.comp_add_right b
  exact hb.bdd_mul (c := C) ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbdd (y + a))

/-- `∫ f(y) f(y − (a − b)) = ∫ f(y + a) f(y + b)` by right-invariance. -/
theorem convolution_shift_group {f : G → ℝ} (a b : G) :
    (∫ y, f y * f (y - (a - b)) ∂μ) = ∫ y, f (y + a) * f (y + b) ∂μ := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => f y * f (y - (a - b))) a
  have harg : ∀ y : G, y + a - (a - b) = y + b := fun y => by abel
  simp only [harg] at h
  exact h.symm

/-- Positive type on a group: `0 ≤ Σᵢⱼ c̄ᵢ cⱼ P(xᵢ − xⱼ)` in `ℂ`. -/
def GroupPositiveType (P : G → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j * (P (x i - x j) : ℂ)

/-- **Convolution squares are positive-type** for integrable bounded real `f` against any
right-invariant measure on an additive commutative group. -/
theorem convolution_square_positive_type_group {f : G → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) :
    GroupPositiveType (fun x => ∫ y, f y * f (y - x) ∂μ) := by
  intro n x c
  have hentry : ∀ i j : Fin n,
      (((∫ y, f y * f (y - (x i - x j)) ∂μ : ℝ)) : ℂ) =
        ∫ y, (((f (y + x i) * f (y + x j) : ℝ)) : ℂ) ∂μ := by
    intro i j
    rw [convolution_shift_group]
    exact integral_ofReal.symm
  have hint : ∀ i j : Fin n, Integrable
      (fun y => (starRingEnd ℂ) (c i) * c j * (((f (y + x i) * f (y + x j) : ℝ)) : ℂ)) μ :=
    fun i j => ((integrable_shift_mul_shift_group hf hbdd (x i) (x j)).ofReal).const_mul _
  simp only [hentry]
  have hswap : ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        ∫ y, (((f (y + x i) * f (y + x j) : ℝ)) : ℂ) ∂μ =
      ∫ y, ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        (((f (y + x i) * f (y + x j) : ℝ)) : ℂ) ∂μ := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_const_mul]
      · exact fun j _ => hint i j
    · exact fun i _ => integrable_finsetSum _ fun j _ => hint i j
  rw [hswap]
  have hpt : ∀ y, ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        (((f (y + x i) * f (y + x j) : ℝ)) : ℂ) =
      ((Complex.normSq (∑ j : Fin n, c j * (f (y + x j) : ℂ)) : ℝ) : ℂ) := by
    intro y
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hpt]
  rw [integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun y => Complex.normSq_nonneg _)

end GppConvolutionSquareGroup
