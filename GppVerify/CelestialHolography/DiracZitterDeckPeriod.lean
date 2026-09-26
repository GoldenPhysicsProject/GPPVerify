import Mathlib.Tactic
import GppVerify.CelestialHolography.DiracSpinCoverIntertwiner

/-!
# Exact Dirac deck recurrence and the zitterbewegung period

For a massive free Dirac mode, write the Compton angular frequency as omega_C.
The spin-cover representation reaches its central deck sign after

  T_deck = pi / omega_C.

The standard zitterbewegung angular frequency is

  omega_Z = 2 omega_C,

so its period is

  T_Z = 2 pi / omega_Z = pi / omega_C = T_deck.

Thus the equality of the zitter period and the Dirac central-deck recurrence
is exact algebra, not a numerical coincidence.

Important scope: this identifies the central deck element inside the free
Dirac Spin(2) representation. It does not by itself identify that element
with every other order-two involution denoted D elsewhere in the project.
Such an identification requires an explicit intertwiner of the relevant
carriers.
-/

namespace GppDiracZitterDeckPeriod

open GppDiracSpinCoverIntertwiner

noncomputable def deckInterval (omegaC : ℝ) : ℝ :=
  Real.pi / omegaC

noncomputable def zitterFrequency (omegaC : ℝ) : ℝ :=
  2 * omegaC

noncomputable def zitterPeriod (omegaC : ℝ) : ℝ :=
  2 * Real.pi / zitterFrequency omegaC

/-- The zitterbewegung period equals the interval required to reach the
central spin-cover deck sign. -/
theorem zitterPeriod_eq_deckInterval
    (omegaC : ℝ) (h : omegaC ≠ 0) :
    zitterPeriod omegaC = deckInterval omegaC := by
  unfold zitterPeriod zitterFrequency deckInterval
  field_simp [h]

/-- Two mass quarter-turns are exactly the central deck action on the finite
Dirac cover carrier. -/
theorem two_mass_quarters_eq_central_deck (psi : ℂ × ℂ) :
    massQuarter (massQuarter psi) = coverAction (-1) psi := by
  rw [massQuarter_sq, coverAction_neg_one]

/-- The central deck recurrence is projectively invisible: multiplying both
components by -1 leaves every homogeneous quadratic magnitude unchanged. -/
theorem central_deck_preserves_normSq_pair (psi : ℂ × ℂ) :
    Complex.normSq (-psi.1) + Complex.normSq (-psi.2)
      = Complex.normSq psi.1 + Complex.normSq psi.2 := by
  simp [Complex.normSq]

end GppDiracZitterDeckPeriod
