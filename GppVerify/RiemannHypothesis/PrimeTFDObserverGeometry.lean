import GppVerify.RiemannHypothesis.PrimeModularCovariance
import Mathlib.Tactic

/-!
# Prime TFD observer-even susceptibility

This module isolates one exact algebraic consequence of the doubled prime TFD
that is useful for the orientation/observer interpretation.

For a prime-like parameter `p>1`, the critical Gibbs mean occupation is

  C_p = 1/(p-1).

The SU(1,1) anomalous covariance satisfies

  A_p^2 = C_p(1+C_p),

and the finite-place transfer/Casimir mass-square coordinate is

  mu_p^2 = 4 C_p = 4/(p-1).

Define the common observer-even susceptibility

  V_p = C_p(1+C_p) = p/(p-1)^2.

Then exactly

  V_p = mu_p^2 (mu_p^2 + 4) / 16.

So the same local parameter controls both the TFD fluctuation scale and the
finite-place mass/discriminant coordinate.  At p=5, mu^2=1 and V=5/16.

These are local algebraic identities.  They do not identify the susceptibility
with a Standard-Model gauge-boson mass, nor do they prove a gravity dictionary
or RH.
-/

namespace GppPrimeTFDObserverGeometry

open GppPrimeModularCovariance

/-- Observer-even TFD susceptibility at a prime-like parameter. -/
noncomputable def observerSusceptibility (p : ℝ) : ℝ :=
  p / (p - 1) ^ 2

/-- Finite-place mass-square coordinate. -/
noncomputable def massSq (p : ℝ) : ℝ :=
  4 / (p - 1)

/-- The observer susceptibility is the Bose covariance variance
`C_p(1+C_p)`. -/
theorem observerSusceptibility_eq_covariance
    (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    observerSusceptibility p =
      thermalCov (1 / p) * (1 + thermalCov (1 / p)) := by
  rw [thermalCov_prime p hp0 hp1]
  unfold observerSusceptibility
  field_simp
  ring

/-- The same susceptibility is determined by the finite-place mass-square
coordinate. -/
theorem observerSusceptibility_eq_massSq
    (p : ℝ) (hp1 : p ≠ 1) :
    observerSusceptibility p =
      massSq p * (massSq p + 4) / 16 := by
  unfold observerSusceptibility massSq
  field_simp [sub_ne_zero.mpr hp1]
  ring

/-- The mass-square coordinate agrees with the existing modular-covariance
normalization. -/
theorem massSq_eq_four_thermalCov
    (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    massSq p = 4 * thermalCov (1 / p) := by
  rw [thermalCov_prime p hp0 hp1]
  unfold massSq
  ring

/-- At the golden prime p=5, the finite-place mass-square coordinate is one. -/
theorem golden_massSq : massSq 5 = 1 := by
  norm_num [massSq]

/-- At p=5 the common susceptibility is 5/16. -/
theorem golden_observerSusceptibility :
    observerSusceptibility 5 = 5 / 16 := by
  norm_num [observerSusceptibility]

/-- The golden identities satisfy the universal mass-susceptibility relation. -/
theorem golden_mass_susceptibility_relation :
    observerSusceptibility 5 =
      massSq 5 * (massSq 5 + 4) / 16 := by
  norm_num [observerSusceptibility, massSq]

end GppPrimeTFDObserverGeometry

#print axioms GppPrimeTFDObserverGeometry.observerSusceptibility_eq_covariance
#print axioms GppPrimeTFDObserverGeometry.observerSusceptibility_eq_massSq
#print axioms GppPrimeTFDObserverGeometry.massSq_eq_four_thermalCov
#print axioms GppPrimeTFDObserverGeometry.golden_massSq
#print axioms GppPrimeTFDObserverGeometry.golden_observerSusceptibility
