import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime
import GppVerify.StandardModel.ChargedKahlerDynamicalSign

/-!
# Compton phase orientation and charged-CAR relative charge

For a massive rest mode the natural positive magnitude is the Compton rate

    omega_C = m c^2 / hbar.

The standard charged-Kahler/CAR construction separates a signed first-order generator

    L = q h

from the positive Hamiltonian `h=|L|`.  In its two-sector standard form, taking
`h = omega_C I` gives

    L = diag(+omega_C,-omega_C),
    q = diag(+1,-1),
    h = diag(+omega_C,+omega_C).

Thus the two microscopic phase/frequency orientations `+/- omega_C` are exactly the two
relative complex-orientation sectors, while physical excitation energy remains positive on
both.  This is the rigorous bridge between the project's oriented Compton phase and standard
charged positive-energy quantization.

What is NOT proved here is that electric charge for every interacting Standard-Model field
is literally generated only by this rest-frequency sign; the theorem is the standard free
charged one-particle structure specialized to the Compton scale.
-/

namespace GppComptonChargedCARAlignmentBridge

open GppOrientationMassTime
open GppChargedKahlerRelativeOrientation
open GppChargedKahlerDynamicalSign

/-- Positive one-particle rest-frequency Hamiltonian. -/
def comptonH (m c hbar : ℝ) : M2C := hPos (comptonFrequency m c hbar)

/-- Signed microscopic rest-frequency generator. -/
def comptonSignedL (m c hbar : ℝ) : M2C := signedL (comptonFrequency m c hbar)

/-- On the positive relative-orientation sector the microscopic frequency is +omega_C. -/
theorem plus_sector_frequency_is_compton (m c hbar : ℝ) :
    comptonSignedL m c hbar *ᵥ plusState =
      (comptonFrequency m c hbar : ℂ) • plusState := by
  exact (signed_frequency_sectors (comptonFrequency m c hbar)).1

/-- On the negative relative-orientation sector it is -omega_C. -/
theorem minus_sector_frequency_is_negative_compton (m c hbar : ℝ) :
    comptonSignedL m c hbar *ᵥ minusState =
      -(comptonFrequency m c hbar : ℂ) • minusState := by
  exact (signed_frequency_sectors (comptonFrequency m c hbar)).2

/-- Yet the positive one-particle Hamiltonian assigns +omega_C to both sectors. -/
theorem both_sectors_positive_compton_magnitude (m c hbar : ℝ) :
    comptonH m c hbar *ᵥ plusState =
      (comptonFrequency m c hbar : ℂ) • plusState ∧
    comptonH m c hbar *ᵥ minusState =
      (comptonFrequency m c hbar : ℂ) • minusState := by
  exact positive_hamiltonian_both_sectors (comptonFrequency m c hbar)

/-- The relative complex-orientation charge grading has the same +/- labels as the signed
    Compton-frequency generator. -/
theorem charge_and_frequency_signs_locked (m c hbar : ℝ) :
    chargeQ *ᵥ plusState = plusState ∧
    comptonSignedL m c hbar *ᵥ plusState =
      (comptonFrequency m c hbar : ℂ) • plusState ∧
    chargeQ *ᵥ minusState = -minusState ∧
    comptonSignedL m c hbar *ᵥ minusState =
      -(comptonFrequency m c hbar : ℂ) • minusState := by
  exact ⟨chargeQ_plus, plus_sector_frequency_is_compton m c hbar,
    chargeQ_minus, minus_sector_frequency_is_negative_compton m c hbar⟩

/-- Capstone: opposite signed microscopic phase rates, opposite relative charge, same positive
    Compton energy magnitude. -/
theorem compton_CAR_orientation_capstone (m c hbar : ℝ) :
    chargeQ *ᵥ plusState = plusState ∧
    chargeQ *ᵥ minusState = -minusState ∧
    comptonH m c hbar *ᵥ plusState =
      (comptonFrequency m c hbar : ℂ) • plusState ∧
    comptonH m c hbar *ᵥ minusState =
      (comptonFrequency m c hbar : ℂ) • minusState := by
  exact ⟨chargeQ_plus, chargeQ_minus,
    (both_sectors_positive_compton_magnitude m c hbar).1,
    (both_sectors_positive_compton_magnitude m c hbar).2⟩

end GppComptonChargedCARAlignmentBridge
