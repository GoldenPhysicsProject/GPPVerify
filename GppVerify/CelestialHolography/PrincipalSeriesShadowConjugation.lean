import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import Mathlib.Tactic

/-!
# Shadow equals conjugation exactly on the scalar celestial principal axis

The positive-real dictionary already proves that `Delta = 2s` transports
`s -> 1-s` to the scalar shadow `Delta -> 2-Delta`, and that `Re s = 1/2`
corresponds to `Re Delta = 1`.

This file closes the equivalent celestial statement directly:

  shadow(Delta) = conjugate(Delta)  <->  Re Delta = 1.

Thus on the principal-series axis the shadow operation is literally complex
conjugation. This is an exact representation-theoretic statement only; it makes
no assertion about zeta zeros.
-/

namespace GppPrincipalShadow

open GppPositiveReal

/-- The project componentwise conjugation commutes with the transport `Delta = 2s`. -/
theorem celestialWeight_conj (s : ℂ) :
    celestialWeight (complexConj s) = complexConj (celestialWeight s) := by
  apply Complex.ext
  · simp [celestialWeight, complexConj]
  · simp [celestialWeight, complexConj]

/-- On the arithmetic critical axis, the transported celestial shadow is conjugation. -/
theorem shadow_eq_conj_on_critical {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    celestialShadow (celestialWeight s) = complexConj (celestialWeight s) := by
  rw [← celestialWeight_intertwines_shadow]
  rw [critical_reflection_eq_conj hs]
  exact celestialWeight_conj s

/-- Direct scalar-celestial characterization: shadow equals conjugation iff `Re Delta = 1`. -/
theorem shadow_eq_conj_iff {Delta : ℂ} :
    celestialShadow Delta = complexConj Delta ↔ Delta.re = 1 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [celestialShadow, complexConj] at hre
    linarith
  · intro hRe
    apply Complex.ext
    · simp [celestialShadow, complexConj, hRe]
    · simp [celestialShadow, complexConj]

end GppPrincipalShadow

#print axioms GppPrincipalShadow.shadow_eq_conj_on_critical
#print axioms GppPrincipalShadow.shadow_eq_conj_iff
