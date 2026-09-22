import Mathlib.Tactic
import GppVerify.StandardModel.CPTMatterOrientationSpine
import GppVerify.StandardModel.ContactDiracHadamardBridge
import GppVerify.StandardModel.MassAsContactExchangeHamiltonian

/-!
# Charge orientation times frequency orientation: contact exchange supplies the time/frequency bit

The oriented-Wilson-line quotient already proves that, for an Abelian conjugate pair, charge
representation sign and oriented-line/time sign enter through the product `q*t`.

The contact/Dirac work now supplies a concrete carrier for the second sign.  In the chiral
basis the canonical contact-factor exchange is

    E = sigma1.

A nonzero rest mass makes the Hamiltonian

    H_rest = m c^2 E.

Hence the symmetric and antisymmetric eigenstates of *geometric factor exchange* are
exactly the positive- and negative-frequency rest branches:

    E |+> = + |+>,
    E |-> = - |->.

So the factor-exchange eigenvalue is a mathematically natural candidate for the
frequency/proper-time orientation sign `t` in the orientation-representation quotient.
Electric charge remains a separate gauge-representation label.

With that dictionary the diagonal transformation

    (charge sign, frequency sign) -> (-charge sign, -frequency sign)

leaves the relational matter character invariant, while either half-flip reverses it.
This file proves the finite algebra.  It does not assert that all non-Abelian gauge
representations reduce to one charge bit, nor that Wigner `T` is identical to the contact
exchange; those require the full spin-gauge bundle construction.
-/

namespace GppChargeFrequencyContactBridge

open GppOrientationMassTime
open GppRelativePhaseDiracEnergy
open GppMassAsContactExchangeHamiltonian
open GppContactDiracHadamardBridge

/-- The two contact-exchange eigenvalues used as the frequency-orientation signs. -/
def positiveFrequencySign : ℝ := 1
def negativeFrequencySign : ℝ := -1

/-- The positive rest branch is the `+1` eigenstate of geometric contact exchange. -/
theorem positive_branch_is_exchange_plus :
    betaRest *ᵥ restPlus = restPlus :=
  betaRest_restPlus

/-- The negative rest branch is the `-1` eigenstate of geometric contact exchange. -/
theorem negative_branch_is_exchange_minus :
    betaRest *ᵥ restMinus = -restMinus :=
  betaRest_restMinus

/-- Relational matter/charge character using the contact-exchange frequency sign. -/
def chargeFrequencyCharacter (q t : ℝ) : ℝ := q * t

/-- Full diagonal reversal preserves the relational character. -/
theorem charge_and_frequency_flip_preserves_character (q t : ℝ) :
    chargeFrequencyCharacter (-q) (-t) = chargeFrequencyCharacter q t := by
  simp [chargeFrequencyCharacter]

/-- Charge-only reversal changes the relational class. -/
theorem charge_only_flip_changes_character (q t : ℝ) :
    chargeFrequencyCharacter (-q) t = - chargeFrequencyCharacter q t := by
  simp [chargeFrequencyCharacter]

/-- Frequency-orientation-only reversal changes the relational class by the same amount. -/
theorem frequency_only_flip_changes_character (q t : ℝ) :
    chargeFrequencyCharacter q (-t) = - chargeFrequencyCharacter q t := by
  simp [chargeFrequencyCharacter]

/-- A charge `q` on the positive-frequency branch and dual charge `-q` on the
negative-frequency branch have the same relational character. -/
theorem diagonal_pair_same_character (q : ℝ) :
    chargeFrequencyCharacter q positiveFrequencySign =
      chargeFrequencyCharacter (-q) negativeFrequencySign := by
  simp [chargeFrequencyCharacter, positiveFrequencySign, negativeFrequencySign]

/-- The Hadamard transform is the explicit change of basis from contact chirality to the
frequency/energy eigenbasis. -/
theorem chirality_to_frequency_basis_intertwiner :
    hadamardRaw * sigma3Contact = betaRest * hadamardRaw :=
  hadamardRaw_intertwines_contact_and_energy

end GppChargeFrequencyContactBridge
