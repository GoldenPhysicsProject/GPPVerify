import GppVerify.CelestialHolography.RaisedBoxOuterMeasurability
import Mathlib.Tactic

/-!
# Raised-box outer fiber bridge

This file starts the final bridge from the measurable full-simplex product
fiber used for outer-coordinate measurability to the nested interval integral
used in the concrete raised-box moment.

The first exact step is set-theoretic: on the physical outer interval, the
section of the full three-simplex at fixed `x1` factors into the middle interval
`0 ≤ x2 ≤ 1-x1` and the already-certified two-dimensional inner simplex strip.
No Fubini or integrability hypothesis is needed for this factorization.
-/

namespace GppRaisedBoxOuterFiberBridge

open MeasureTheory
open GppRaisedBoxConcreteMoment
open GppRaisedBoxOuterMeasurability

/-- On the physical outer interval, membership in the full grouped simplex
section is equivalent to membership of `x2` in its affine interval together
with membership of `(x2,x3)` in the inner simplex strip. -/
theorem fullSimplexSet_section_iff
    {x1 x2 x3 : ℝ} (hx1 : x1 ∈ Set.Icc (0 : ℝ) 1) :
    (x1, (x2, x3)) ∈ fullSimplexSet ↔
      x2 ∈ Set.Icc (0 : ℝ) (1 - x1) ∧
        (x2, x3) ∈ innerSimplexStrip x1 := by
  rcases hx1 with ⟨hx10, hx11⟩
  constructor
  · intro h
    rcases h with ⟨⟨⟨hx10', hx20⟩, hx30⟩, hsum⟩
    change 0 ≤ x1 at hx10'
    change 0 ≤ x2 at hx20
    change 0 ≤ x3 at hx30
    change x1 + x2 + x3 ≤ 1 at hsum
    constructor
    · constructor
      · exact hx20
      · linarith
    · constructor
      · exact hx30
      · linarith
  · rintro ⟨⟨hx20, hx2hi⟩, hx30, h23⟩
    change 0 ≤ x3 at hx30
    change x2 + x3 ≤ 1 - x1 at h23
    exact ⟨⟨⟨hx10, hx20⟩, hx30⟩, by
      change x1 + x2 + x3 ≤ 1
      linarith⟩

/-- Pointwise factorization of the full-simplex indicator along a physical
outer section.  This is the algebraic interface needed before applying Fubini
to identify the product fiber with the nested `x2`/`x3` interval integral. -/
theorem fullSimplexIndicator_section_factor
    (ε S T : ℝ) {x1 x2 x3 : ℝ}
    (hx1 : x1 ∈ Set.Icc (0 : ℝ) 1) :
    (fullSimplexSet.indicator
      (fun q : ℝ × (ℝ × ℝ) =>
        integrand ε S T q.1 q.2.1 q.2.2)) (x1, (x2, x3)) =
      (Set.Icc (0 : ℝ) (1 - x1)).indicator
        (fun y : ℝ =>
          (innerSimplexStrip x1).indicator
            (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)
            (y, x3)) x2 := by
  by_cases hfull : (x1, (x2, x3)) ∈ fullSimplexSet
  · have hfac := (fullSimplexSet_section_iff hx1).1 hfull
    simp [Set.indicator_of_mem hfull,
      Set.indicator_of_mem hfac.1, Set.indicator_of_mem hfac.2]
  · have hnot : ¬ (x2 ∈ Set.Icc (0 : ℝ) (1 - x1) ∧
      (x2, x3) ∈ innerSimplexStrip x1) := by
      exact fun h => hfull ((fullSimplexSet_section_iff hx1).2 h)
    by_cases hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)
    · have hstrip : (x2, x3) ∉ innerSimplexStrip x1 := by
        intro hs
        exact hnot ⟨hx2, hs⟩
      simp [Set.indicator_of_not_mem hfull,
        Set.indicator_of_mem hx2, Set.indicator_of_not_mem hstrip]
    · simp [Set.indicator_of_not_mem hfull, Set.indicator_of_not_mem hx2]

/-- Once the full two-dimensional section is known to be integrable, Fubini
identifies its product integral exactly with the outer closed-interval indicator
of the already-certified measurable inner strip integral.  This theorem isolates
the remaining analytic obligation cleanly: only the `Integrable` certificate is
left to prove from the raised-box majorant. -/
theorem fullSimplexFiberIntegral_eq_iteratedStrip
    (ε S T x1 : ℝ)
    (hx1 : x1 ∈ Set.Icc (0 : ℝ) 1)
    (hInt : Integrable
      (fun p : ℝ × ℝ =>
        (fullSimplexSet.indicator
          (fun q : ℝ × (ℝ × ℝ) =>
            integrand ε S T q.1 q.2.1 q.2.2)) (x1, p))) :
    (∫ p : ℝ × ℝ,
      (fullSimplexSet.indicator
        (fun q : ℝ × (ℝ × ℝ) =>
          integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)) =
      ∫ x2 : ℝ,
        (Set.Icc (0 : ℝ) (1 - x1)).indicator
          (fun y : ℝ =>
            ∫ x3 : ℝ,
              ((innerSimplexStrip x1).indicator
                (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2))
                (y, x3)) x2 := by
  let f : ℝ × ℝ → ℝ := fun p =>
    (fullSimplexSet.indicator
      (fun q : ℝ × (ℝ × ℝ) =>
        integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)
  have hIntProd : Integrable f (volume.prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact hInt
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.integral_prod f hIntProd]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x2
  by_cases hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)
  · rw [Set.indicator_of_mem hx2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x3
    simpa [f, Set.indicator_of_mem hx2] using
      (fullSimplexIndicator_section_factor ε S T hx1 (x2 := x2) (x3 := x3))
  · rw [Set.indicator_of_not_mem hx2]
    have hfzero : ∀ x3 : ℝ, f (x2, x3) = 0 := by
      intro x3
      simpa [f, Set.indicator_of_not_mem hx2] using
        (fullSimplexIndicator_section_factor ε S T hx1 (x2 := x2) (x3 := x3))
    simp_rw [hfzero]
    simp

end GppRaisedBoxOuterFiberBridge

#print axioms GppRaisedBoxOuterFiberBridge.fullSimplexSet_section_iff
#print axioms GppRaisedBoxOuterFiberBridge.fullSimplexIndicator_section_factor
#print axioms GppRaisedBoxOuterFiberBridge.fullSimplexFiberIntegral_eq_iteratedStrip