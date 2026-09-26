import Mathlib.Tactic
import GppVerify.RiemannHypothesis.RiemannCayleyUnitarityBoundary

/-!
# Reciprocal contraction forces the Riemann critical line

For the Cayley coordinate

  beta(s) = (s - 1) / s,

functional-equation reflection `s -> 1-s` reciprocates the squared modulus.
Consequently a positive Hilbert realization in which BOTH reflected channels are
contractive cannot support an off-critical parameter: a contraction and its reciprocal
can both have norm at most one only at unit modulus.

This file proves only the finite scalar core.  It does not assert that the global zeta
scattering / Nyman--Burnol channel supplies the two contractivity hypotheses.  Producing
those hypotheses from zero-independent arithmetic data is the hard RH theorem.
-/

namespace GppReciprocalContractionCriticalLine

open GppRiemannCayleyUnitarityBoundary

/-- Two positive reciprocal real numbers which are both at most one must both equal one. -/
theorem reciprocal_pair_eq_one
    {x y : ℝ} (hx : 0 < x)
    (hxy : x * y = 1) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    x = 1 ∧ y = 1 := by
  have hone_le_x : 1 ≤ x := by
    by_contra h
    have hxlt : x < 1 := lt_of_not_ge h
    have hxylt : x * y < 1 := by
      calc
        x * y ≤ x * 1 := mul_le_mul_of_nonneg_left hy1 (le_of_lt hx)
        _ < 1 := by simpa using hxlt
    linarith
  have hxEq : x = 1 := le_antisymm hx1 hone_le_x
  have hyEq : y = 1 := by
    rw [hxEq, one_mul] at hxy
    exact hxy
  exact ⟨hxEq, hyEq⟩

/--
**Two-sheet contraction theorem.**

If a point `s = sigma + i t` and its functional-equation reflection `1-s`
are both contractive in the SAME Cayley norm, then `sigma = 1/2`.

The exclusions encoded by `hden` and `hrefden` are just the nonzero denominators
needed by the Cayley chart.
-/
theorem both_cayley_channels_contract_forces_critical
    (sigma t : ℝ)
    (hden : 0 < sigma^2 + t^2)
    (hrefden : 0 < (1 - sigma)^2 + t^2)
    (hcontract : cayleyNormSq sigma t ≤ 1)
    (hrefcontract : cayleyNormSq (1 - sigma) t ≤ 1) :
    sigma = (1 / 2 : ℝ) := by
  by_contra hcrit
  rcases lt_or_gt_of_ne hcrit with hslt | hsgt
  · have hgt : 1 < cayleyNormSq sigma t :=
      (one_lt_cayley_iff sigma t hden).2 hslt
    linarith
  · have hrefgt : 1 < cayleyNormSq (1 - sigma) t :=
      (one_lt_cayley_iff (1 - sigma) t hrefden).2 (by linarith)
    linarith

/-- On the critical line both reflected Cayley channels have exactly unit norm. -/
theorem critical_gives_two_unit_channels
    (sigma t : ℝ)
    (hden : 0 < sigma^2 + t^2)
    (hrefden : 0 < (1 - sigma)^2 + t^2)
    (hcrit : sigma = (1 / 2 : ℝ)) :
    cayleyNormSq sigma t = 1 ∧
      cayleyNormSq (1 - sigma) t = 1 := by
  constructor
  · exact (cayley_eq_one_iff sigma t hden).2 hcrit
  · exact (cayley_eq_one_iff (1 - sigma) t hrefden).2 (by linarith)

/-- Exact iff: simultaneous contractivity of the reflected Cayley pair is the critical line. -/
theorem two_sheet_contractivity_iff_critical
    (sigma t : ℝ)
    (hden : 0 < sigma^2 + t^2)
    (hrefden : 0 < (1 - sigma)^2 + t^2) :
    (cayleyNormSq sigma t ≤ 1 ∧
      cayleyNormSq (1 - sigma) t ≤ 1) ↔
      sigma = (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨h1,h2⟩
    exact both_cayley_channels_contract_forces_critical sigma t hden hrefden h1 h2
  · intro hcrit
    rcases critical_gives_two_unit_channels sigma t hden hrefden hcrit with ⟨h1,h2⟩
    exact ⟨le_of_eq h1, le_of_eq h2⟩

end GppReciprocalContractionCriticalLine
