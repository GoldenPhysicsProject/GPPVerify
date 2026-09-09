import Mathlib.Tactic
import GppVerify.StandardModel.CPTPairedOrientationState

/-!
# Antiunitary CPT pairing is not the same condition as diagonal gauge invariance

Two structures have appeared on the (++/--) pair:

* the linear diagonal deck swap `D(a,b)=(b,a)`;
* the anti-linear CPT-core pairing `Theta(a,b)=(conj b,conj a)`.

They have the same permutation of the two labels but are mathematically different because
`Theta` also complex-conjugates amplitudes.  This file proves the distinction explicitly.

`Theta`-fixed states need not be `D`-even, and `D`-even states need not be `Theta`-fixed.
The combined conditions force an equal pair with real amplitude.  Therefore the project
must choose carefully between three possibilities: diagonal reversal as gauge/deck
redundancy, CPT as an antiunitary global symmetry, or both as distinct structures.  They
must not be collapsed merely because both exchange the same sign labels.
-/

namespace GppCPTvsDiagonalGaugeSeparation

open scoped ComplexConjugate
open GppCPTPairedOrientationState

/-- Linear label swap, without complex conjugation. -/
def deckSwap (psi : OrientationPair) : OrientationPair := (psi.2,psi.1)

/-- The deck swap is involutive. -/
theorem deckSwap_sq (psi : OrientationPair) : deckSwap (deckSwap psi) = psi := by
  rcases psi with ⟨a,b⟩
  rfl

/-- CPT-core pairing is conjugation after the linear deck swap. -/
theorem theta_eq_conj_after_deck (psi : OrientationPair) :
    theta psi = (conj (deckSwap psi).1, conj (deckSwap psi).2) := by
  rcases psi with ⟨a,b⟩
  rfl

/-- Counterexample: a Theta-fixed state can be deck-odd rather than deck-even. -/
theorem theta_fixed_not_imply_deck_even :
    let psi : OrientationPair := (Complex.I, -Complex.I)
    theta psi = psi ∧ deckSwap psi ≠ psi := by
  dsimp
  constructor
  · simp [theta]
  · intro h
    have h0 := congrArg Prod.fst h
    simp [deckSwap] at h0

/-- Conversely, a deck-even state need not be Theta-fixed. -/
theorem deck_even_not_imply_theta_fixed :
    let psi : OrientationPair := (Complex.I, Complex.I)
    deckSwap psi = psi ∧ theta psi ≠ psi := by
  dsimp
  constructor
  · rfl
  · intro h
    have h0 := congrArg Prod.fst h
    simp [theta] at h0

/-- If both conditions hold, the two amplitudes coincide and are real. -/
theorem theta_fixed_and_deck_even_force_real_equal
    (psi : OrientationPair)
    (hTheta : theta psi = psi)
    (hDeck : deckSwap psi = psi) :
    psi.2 = psi.1 ∧ conj psi.1 = psi.1 := by
  have heq : psi.2 = psi.1 := by
    have h := congrArg Prod.fst hDeck
    simpa [deckSwap] using h
  have hpartner := theta_fixed_partner psi hTheta
  constructor
  · exact heq
  · rw [← heq]
    exact hpartner.symm

end GppCPTvsDiagonalGaugeSeparation
