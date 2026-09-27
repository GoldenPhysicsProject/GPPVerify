import Mathlib.Tactic
import GppVerify.StandardModel.CPTPairedOrientationState
import GppVerify.StandardModel.CPTvsDiagonalGaugeSeparation

/-!
# Kähler--Dirac Majorana two-sheet pairing: exact finite core and prior-art bridge

Boyle--Deng, `CPT-Symmetric Kähler-Dirac Fermions` (arXiv:2511.11548), propose that the
Lorentzian Kähler--Dirac field lives on two PT-related sheets, equivalently related by
`i <-> -i`, and impose a KD-Majorana reality condition.  Their condition pairs every
particle on one sheet with the charge-conjugate mirror particle on the other; they explicitly
describe the resulting excitation as an invariant/symmetric combination of the two sheets.

The project's previously defined anti-linear orientation pairing

    Theta(a,b) = (conj b, conj a)

is exactly the minimal two-amplitude algebra of such a reality condition.  Hence the equal
Born weights previously derived from `Theta psi = psi` are NOT by themselves a novel
prediction: they are the generic consequence of an anti-linear two-sheet reality condition
of this form.

What remains open/new in the present programme is to identify the geometric carrier of the
two amplitudes with the specific gauge/frequency complex orientations, Grassmannian/twistor
structure, and black-mirror horizon geometry.  This file deliberately records the prior-art
collision so the formal library cannot silently treat the two-sheet Majorana pairing as a
new theorem of the project.
-/

namespace GppKDMajoranaOrientationBridge

open scoped ComplexConjugate
open GppCPTPairedOrientationState
open GppCPTvsDiagonalGaugeSeparation

/-- Minimal KD-Majorana reality condition on a two-sheet amplitude pair. -/
def kdMajorana (psi : OrientationPair) : Prop := theta psi = psi

/-- The reality condition makes the second sheet the conjugate partner of the first. -/
theorem kdMajorana_partner (psi : OrientationPair) (h : kdMajorana psi) :
    psi.2 = conj psi.1 := by
  exact theta_fixed_partner psi h

/-- Therefore the two sheet amplitudes have equal Born weight. -/
theorem kdMajorana_equal_weights (psi : OrientationPair) (h : kdMajorana psi) :
    Complex.normSq psi.1 = Complex.normSq psi.2 := by
  exact theta_fixed_equal_normSq psi h

/-- If normalized, the minimal two-sheet reality pair carries exactly one-half weight on
    each sheet. -/
theorem kdMajorana_half_weights (psi : OrientationPair)
    (h : kdMajorana psi)
    (hnorm : Complex.normSq psi.1 + Complex.normSq psi.2 = 1) :
    Complex.normSq psi.1 = (1/2 : ℝ) ∧
    Complex.normSq psi.2 = (1/2 : ℝ) := by
  exact theta_fixed_half_weights psi h hnorm

/-- Every amplitude `a` determines its canonical two-sheet Majorana pair `(a,conj a)`. -/
theorem canonical_kdMajorana_pair (a : ℂ) : kdMajorana (a,conj a) := by
  exact canonical_theta_fixed a

/-- Important separation: a KD-Majorana anti-linear reality condition is not the same as
    imposing the linear deck-even condition. -/
theorem kdMajorana_not_same_as_linear_deck_constraint :
    let psi : OrientationPair := (Complex.I,-Complex.I)
    kdMajorana psi ∧ deckSwap psi ≠ psi := by
  exact theta_fixed_not_imply_deck_even

/-- Capstone: equal two-sheet weights follow from the anti-linear reality condition, while
    no linear gauge/deck identification is implied. -/
theorem kdMajorana_pairing_capstone (psi : OrientationPair)
    (h : kdMajorana psi)
    (hnorm : Complex.normSq psi.1 + Complex.normSq psi.2 = 1) :
    psi.2 = conj psi.1 ∧
    Complex.normSq psi.1 = (1/2 : ℝ) ∧
    Complex.normSq psi.2 = (1/2 : ℝ) := by
  rcases kdMajorana_half_weights psi h hnorm with ⟨h1,h2⟩
  exact ⟨kdMajorana_partner psi h,h1,h2⟩

end GppKDMajoranaOrientationBridge
