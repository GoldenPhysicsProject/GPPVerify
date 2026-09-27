import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import Mathlib.Tactic

/-!
# Arithmetic Osterwalder--Schrader reflection on the Mellin parameter

For multiplicative position `x > 0`, inversion `x -> x⁻¹` becomes ordinary
Euclidean-time reflection after `t = log x`.  On the centered Mellin line the
corresponding anti-linear spectral reflection is

  s -> 1 - conjugate(s).

Its fixed set is exactly `Re s = 1/2`.  Under the celestial transport `Delta = 2s`
it becomes `Delta -> 2 - conjugate(Delta)`.

This file proves only the exact complex-algebra skeleton.  It does not assert
reflection positivity of the arithmetic explicit formula and therefore makes no
claim toward RH by itself.
-/

namespace GppArithmeticOS

open GppPositiveReal

/-- Anti-linear arithmetic reflection: functional-equation reflection composed
with complex conjugation. -/
def osReflection (s : ℂ) : ℂ := criticalReflection (complexConj s)

/-- The componentwise conjugation used by the project is involutive. -/
theorem complexConj_involutive (s : ℂ) :
    complexConj (complexConj s) = s := by
  apply Complex.ext <;> simp [complexConj]

/-- Arithmetic OS reflection is an involution. -/
theorem osReflection_involutive (s : ℂ) :
    osReflection (osReflection s) = s := by
  apply Complex.ext
  · simp [osReflection, criticalReflection, complexConj]
  · simp [osReflection, criticalReflection, complexConj]

/-- The fixed locus of the anti-linear reflection is exactly the critical line. -/
theorem osReflection_eq_self_iff {s : ℂ} :
    osReflection s = s ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [osReflection, criticalReflection, complexConj] at hre
    linarith
  · intro hs
    apply Complex.ext
    · simp [osReflection, criticalReflection, complexConj, hs]
      norm_num
    · simp [osReflection, criticalReflection, complexConj]

/-- Centering at one half converts arithmetic OS reflection into sign reversal
plus conjugation.  This is the exact Mellin-space analogue of `t -> -t`. -/
theorem osReflection_centered (s : ℂ) :
    osReflection s - (1 / 2 : ℂ) =
      -complexConj (s - (1 / 2 : ℂ)) := by
  apply Complex.ext
  · simp [osReflection, criticalReflection, complexConj]
    ring
  · simp [osReflection, criticalReflection, complexConj]

/-- Under `Delta = 2s`, arithmetic OS reflection becomes celestial shadow
composed with conjugation. -/
theorem celestialWeight_intertwines_osReflection (s : ℂ) :
    celestialWeight (osReflection s) =
      celestialShadow (complexConj (celestialWeight s)) := by
  apply Complex.ext
  · simp [celestialWeight, celestialShadow, osReflection, criticalReflection, complexConj]
    ring
  · simp [celestialWeight, celestialShadow, osReflection, criticalReflection, complexConj]

end GppArithmeticOS

#print axioms GppArithmeticOS.osReflection_involutive
#print axioms GppArithmeticOS.osReflection_eq_self_iff
#print axioms GppArithmeticOS.osReflection_centered
#print axioms GppArithmeticOS.celestialWeight_intertwines_osReflection
