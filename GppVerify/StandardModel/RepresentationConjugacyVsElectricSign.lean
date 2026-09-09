import Mathlib.Tactic

/-!
# Matter/antimatter conjugacy orientation is not the sign of electric charge

A crucial correction for the orientation programme: ordinary matter contains species of
both electric-charge signs (for example proton-like `+e` and electron-like `-e` species).
Therefore the microscopic sign which distinguishes a representation `R` from its conjugate
`R*` cannot be identified universally with the numerical sign of electric charge.

Instead let `c=+/-1` denote representation-conjugacy orientation for a fixed species whose
reference electric charge is `q0`.  The observed fixed-sheet charge is `c*q0`.  Conjugating
the species changes `c`, while different matter species can have different `q0` signs.

This elementary distinction is necessary before the cosmological `c*t` matter character can
be compared with baryon/lepton asymmetry or the full Standard Model representation content.
-/

namespace GppRepresentationConjugacyVsElectricSign

/-- Electric charge of a species with reference charge `q0` and conjugacy orientation `c`. -/
def electricCharge (q0 c : ℝ) : ℝ := c*q0

/-- Conjugating one fixed species reverses its electric charge. -/
theorem conjugation_flips_species_charge (q0 c : ℝ) :
    electricCharge q0 (-c) = -electricCharge q0 c := by
  simp [electricCharge]
  ring

/-- Two ordinary matter species may have opposite electric signs while sharing the same
    representation-orientation label `c=+1`. -/
theorem same_matter_orientation_opposite_electric_signs (e : ℝ) :
    electricCharge e 1 = e ∧ electricCharge (-e) 1 = -e := by
  simp [electricCharge]

/-- A proton/electron-like matter pair is electrically neutral although both species have
    the same matter-conjugacy orientation. -/
theorem matter_pair_can_be_electrically_neutral (e : ℝ) :
    electricCharge e 1 + electricCharge (-e) 1 = 0 := by
  simp [electricCharge]

/-- The fully conjugate antimatter pair is electrically neutral as well. -/
theorem antimatter_pair_can_be_electrically_neutral (e : ℝ) :
    electricCharge e (-1) + electricCharge (-e) (-1) = 0 := by
  simp [electricCharge]

/-- Thus electric neutrality does not imply a matter/antimatter balance. -/
theorem neutrality_does_not_fix_conjugacy_orientation (e : ℝ) :
    electricCharge e 1 + electricCharge (-e) 1 = 0 ∧
    electricCharge e (-1) + electricCharge (-e) (-1) = 0 := by
  exact ⟨matter_pair_can_be_electrically_neutral e,
    antimatter_pair_can_be_electrically_neutral e⟩

end GppRepresentationConjugacyVsElectricSign
