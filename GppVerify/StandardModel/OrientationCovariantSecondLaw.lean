import Mathlib.Tactic

/-!
# Orientation-covariant second-law sign core

Finite algebra accompanying Daniel Toupin,
"Which Way Is Forward?", v20.

The paper distinguishes an arbitrary external coordinate orientation from the
future orientation selected by a lifted history. If t in {+1,-1} is the
temporal-orientation sign and r = dS/dlambda is the coordinate entropy rate,
the internal/oriented rate is

  D_t S = t*r.

Complete reversal sends (t,r) -> (-t,-r), so t*r is invariant although the
coordinate rate changes sign. A paired orientation-symmetric state therefore
has zero signed coordinate rate while the two internal rates agree.

This file formalizes only that finite sign algebra. It does not derive
thermodynamic entropy, a low-entropy boundary condition, decoherence, or the
many-body origin of the macroscopic record arrow.
-/

namespace GppOrientationCovariantSecondLaw

/-- Relational particle/antiparticle grading. -/
def relationalChi (q t : ℝ) : ℝ := q * t

/-- Internal entropy-production rate relative to temporal orientation t. -/
def orientedEntropyRate (t r : ℝ) : ℝ := t * r

/-- Complete q,t reversal preserves the relational grading. -/
theorem diagonal_reversal_preserves_chi (q t : ℝ) :
    relationalChi (-q) (-t) = relationalChi q t := by
  simp [relationalChi]

/-- A single q or t half flip reverses the relational grading. -/
theorem either_half_flip_reverses_chi (q t : ℝ) :
    relationalChi (-q) t = - relationalChi q t ∧
    relationalChi q (-t) = - relationalChi q t := by
  constructor <;> simp [relationalChi]

/-- Complete temporal reversal changes both orientation and coordinate rate,
leaving the internal/oriented entropy rate unchanged. -/
theorem complete_reversal_preserves_oriented_rate (t r : ℝ) :
    orientedEntropyRate (-t) (-r) = orientedEntropyRate t r := by
  simp [orientedEntropyRate]

/-- Opposite coordinate entropy rates cancel in an equally weighted pair. -/
theorem paired_coordinate_rates_cancel (r : ℝ) :
    (r + (-r)) / 2 = 0 := by
  ring

/-- The two opposite lifts assign the same internal entropy-production rate. -/
theorem paired_oriented_rates_equal (r : ℝ) :
    orientedEntropyRate (1 : ℝ) r =
      orientedEntropyRate (-1 : ℝ) (-r) := by
  simp [orientedEntropyRate]

/-- Their equally weighted oriented average equals the positive-side rate. -/
theorem paired_oriented_average (r : ℝ) :
    (orientedEntropyRate (1 : ℝ) r +
      orientedEntropyRate (-1 : ℝ) (-r)) / 2 = r := by
  simp [orientedEntropyRate]

/-- If the positive lift has nonnegative coordinate entropy rate, both lifts
have nonnegative entropy production in their own future orientation. -/
theorem paired_second_law {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ orientedEntropyRate (1 : ℝ) r ∧
    0 ≤ orientedEntropyRate (-1 : ℝ) (-r) := by
  simpa [orientedEntropyRate] using And.intro hr hr

/-- Package the exact sign content used in the time-symmetric entropy argument. -/
theorem time_symmetric_entropy_sign_capstone {r : ℝ} (hr : 0 ≤ r) :
    (r + (-r)) / 2 = 0 ∧
    orientedEntropyRate (1 : ℝ) r =
      orientedEntropyRate (-1 : ℝ) (-r) ∧
    0 ≤ orientedEntropyRate (1 : ℝ) r ∧
    0 ≤ orientedEntropyRate (-1 : ℝ) (-r) := by
  refine ⟨paired_coordinate_rates_cancel r,
    paired_oriented_rates_equal r, ?_⟩
  exact paired_second_law hr

end GppOrientationCovariantSecondLaw
