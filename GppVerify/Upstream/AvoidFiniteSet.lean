/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A point of a unit interval far from a finite set

If `F` is a finite set of reals with at most `N` elements, every interval `[T, T + 1]` contains a
point whose distance to every element of `F` is at least `1 / (2 (N + 1))`. This is the
pigeonhole step that selects "good heights" in the contour shift of the explicit formula: the
ordinates of the zeros in a bounded region are finitely many, polynomially many in the height, and
a horizontal line can be placed at polynomial distance from all of them.
-/

open MeasureTheory Set

namespace Real

/-- **A point of `[T, T+1]` at distance at least `1 / (2 (N+1))` from every element of a finite
set with at most `N` elements.** -/
theorem exists_mem_Icc_far_from_finset (T : ℝ) (F : Finset ℝ) {N : ℕ} (hF : F.card ≤ N) :
    ∃ t ∈ Icc T (T + 1), ∀ x ∈ F, 1 / (2 * ((N : ℝ) + 1)) ≤ |t - x| := by
  set δ : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  by_contra hcon
  push Not at hcon
  have hsub : Icc T (T + 1) ⊆ ⋃ x ∈ F, Ioo (x - δ) (x + δ) := by
    intro t ht
    obtain ⟨x, hx, hlt⟩ := hcon t ht
    refine mem_biUnion hx ?_
    rw [mem_Ioo]
    have := abs_lt.1 hlt
    constructor <;> linarith [this.1, this.2]
  have h1 : volume (Icc T (T + 1)) ≤ ∑ x ∈ F, volume (Ioo (x - δ) (x + δ)) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le F _)
  have h2 : ∀ x : ℝ, volume (Ioo (x - δ) (x + δ)) = ENNReal.ofReal (2 * δ) := by
    intro x
    rw [Real.volume_Ioo]
    congr 1
    ring
  simp only [h2, Real.volume_Icc, Finset.sum_const, nsmul_eq_mul] at h1
  have h3 : ENNReal.ofReal (T + 1 - T) = ENNReal.ofReal 1 := by congr 1; ring
  rw [h3] at h1
  have h4 : (F.card : ENNReal) * ENNReal.ofReal (2 * δ) = ENNReal.ofReal (F.card * (2 * δ)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ F.card), ENNReal.ofReal_natCast]
  rw [h4] at h1
  have h5 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have h6 : (F.card : ℝ) * (2 * δ) < 1 := by
    rw [hδ]
    have hc : (F.card : ℝ) ≤ N := by exact_mod_cast hF
    rw [show (F.card : ℝ) * (2 * (1 / (2 * ((N : ℝ) + 1)))) = F.card / ((N : ℝ) + 1) by
      field_simp]
    rw [div_lt_one (by positivity)]
    linarith
  linarith

end Real
