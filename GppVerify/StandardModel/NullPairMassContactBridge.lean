import Mathlib.Tactic
import GppVerify.StandardModel.SpinorMassBridge
import GppVerify.StandardModel.MassAsContactExchangeHamiltonian

/-!
# Two null spinor roots -> mass -> contact exchange -> Compton/zitter clock

A massive timelike momentum is represented in the project by a pair of null spinor roots.
Their symplectic area has modulus equal to the physical mass on the positive mass shell:

    |<lambda1 lambda2>| = m.

Independently, the rest Dirac Hamiltonian was shown to be the canonical contact-factor
exchange multiplied by `m c^2`:

    H_rest = m c^2 E_contact.

Combining the two exact bridges gives

    H_rest = c^2 |<lambda1 lambda2>| E_contact,

and hence

    omega_C = c^2 |<lambda1 lambda2>| / hbar,
    omega_zitt = 2 c^2 |<lambda1 lambda2>| / hbar.

Thus, within the already formalized massive-spinor chart, the intrinsic clock rate is fixed
by the oriented area spanned by the two null roots.  In the collinear/massless limit that
area vanishes and the rest exchange clock disappears.

This does not derive which timelike momentum Nature chooses; it proves the exact chain from
a given positive-mass-shell momentum to its null-root area, rest coupling, and clock rates.
-/

namespace GppNullPairMassContactBridge

open GppMassOrientationCoupling
open GppMassAsContactExchangeHamiltonian
open GppOrientationMassTime

/-- On shell, the rest-energy coefficient is `c^2` times the null-root symplectic area norm. -/
theorem restEnergyScale_eq_spinorArea
    {p00 p11 m c : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    restEnergyScale m c =
      (((‖spinorArea p00 p11 p01‖ * c^2 : ℝ) : ℂ)) := by
  have harea := spinorArea_norm_eq_mass hp00 hdet hm hmass
  simp [restEnergyScale, harea]

/-- The rest Hamiltonian coupling is therefore the null-root area times `c^2` multiplying
contact exchange. -/
theorem restHamiltonian_from_nullRootArea
    {p00 p11 m c : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01)
    (psi : Fin 2 → ℂ) :
    restHamiltonianAct m c psi =
      (((‖spinorArea p00 p11 p01‖ * c^2 : ℝ) : ℂ)) •
        (GppRelativePhaseDiracEnergy.betaRest *ᵥ psi) := by
  rw [restHamiltonianAct]
  rw [restEnergyScale_eq_spinorArea hp00 hdet hm hmass]

/-- The reduced Compton frequency is the null-root area converted to an energy by `c^2`
and divided by `hbar`. -/
theorem comptonFrequency_from_nullRootArea
    {p00 p11 m c hbar : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    comptonFrequency m c hbar =
      ‖spinorArea p00 p11 p01‖ * c^2 / hbar := by
  have harea := spinorArea_norm_eq_mass hp00 hdet hm hmass
  simp [comptonFrequency, harea]

/-- The zitter beat is twice that geometric clock rate. -/
theorem zitterFrequency_from_nullRootArea
    {p00 p11 m c hbar : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    zitterFrequency m c hbar =
      2 * (‖spinorArea p00 p11 p01‖ * c^2 / hbar) := by
  rw [zitterFrequency, comptonFrequency_from_nullRootArea hp00 hdet hm hmass]

end GppNullPairMassContactBridge
