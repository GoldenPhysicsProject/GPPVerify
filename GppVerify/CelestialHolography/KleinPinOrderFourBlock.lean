import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinSpinorIncidence

/-!
# Eight-dimensional chiral block algebra for an order-four Klein/Pin lift

The complex Clifford module for a six-dimensional split carrier has the Fock-model
shape `S = SPlus ⊕ SMinus`, with each chiral half four-dimensional.  In a convenient
basis an odd lift is represented by two maps

  MPlus  : SPlus  -> SMinus,
  MMinus : SMinus -> SPlus,

whose coordinate blocks are

  MPlus  = [[ 1, 0, 0, 0],
            [ 0, 0, 1, 0],
            [ 0,-1, 0, 0],
            [ 0, 0, 0, 1]],

  MMinus = [[-1, 0, 0, 0],
            [ 0, 0,-1, 0],
            [ 0, 1, 0, 0],
            [ 0, 0, 0,-1]].

Both two-step compositions are the same involution

  Gamma = diag(-1,+1,+1,-1),

so the full odd operator on the direct sum has fourth power one.  This file proves only
that exact finite block algebra.  The identification of these coordinates with a chosen
Pin lift of the global Klein transformation is a separate Clifford-basis theorem; it is
not smuggled into the definitions below.
-/

namespace GppKleinPinOrderFourBlock

open GppKleinSpinorIncidence
open GppTwistorAnnihilatorIncidence

/-- We use the already-established four-component twistor carrier for each chiral half. -/
abbrev HalfSpin := V4
abbrev FullSpin := HalfSpin × HalfSpin

/-- Even-to-odd chiral block. -/
def mPlus (z : HalfSpin) : HalfSpin :=
  (z.1, z.2.2.1, -z.2.1, z.2.2.2)

/-- Odd-to-even chiral block. -/
def mMinus (z : HalfSpin) : HalfSpin :=
  (-z.1, -z.2.2.1, z.2.1, -z.2.2.2)

/-- The common square on either chiral half. -/
def gammaBlock (z : HalfSpin) : HalfSpin :=
  (-z.1, z.2.1, z.2.2.1, -z.2.2.2)

/-- `MMinus MPlus = Gamma` on the even half. -/
theorem mMinus_mPlus (z : HalfSpin) :
    mMinus (mPlus z) = gammaBlock z := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [mPlus, mMinus, gammaBlock]

/-- `MPlus MMinus = Gamma` on the odd half. -/
theorem mPlus_mMinus (z : HalfSpin) :
    mPlus (mMinus z) = gammaBlock z := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [mPlus, mMinus, gammaBlock]

/-- The square block is an involution. -/
theorem gammaBlock_sq (z : HalfSpin) :
    gammaBlock (gammaBlock z) = z := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [gammaBlock]

/-- The full odd operator exchanges the two four-component chiral halves. -/
def pinQuarterLift (psi : FullSpin) : FullSpin :=
  (mMinus psi.2, mPlus psi.1)

/-- Squaring the full eight-component lift gives `Gamma` on both chiral halves. -/
theorem pinQuarterLift_sq (psi : FullSpin) :
    pinQuarterLift (pinQuarterLift psi) =
      (gammaBlock psi.1, gammaBlock psi.2) := by
  rcases psi with ⟨sPlus,sMinus⟩
  simp [mPlus, mMinus, gammaBlock, pinQuarterLift]

/-- Four applications close exactly on the eight-component spin carrier.  The proof is
expanded componentwise so it does not depend on rewrite-order heuristics. -/
theorem pinQuarterLift_four (psi : FullSpin) :
    pinQuarterLift (pinQuarterLift (pinQuarterLift (pinQuarterLift psi))) = psi := by
  rcases psi with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  simp [mPlus, mMinus, gammaBlock, pinQuarterLift]

/-- The order-four algebra in one package: the lift exchanges 4+4 chiral components,
its square is the nontrivial diagonal involution, and its fourth power is identity. -/
theorem pin_order_four_package (psi : FullSpin) :
    pinQuarterLift (pinQuarterLift psi) =
        (gammaBlock psi.1, gammaBlock psi.2) ∧
    pinQuarterLift (pinQuarterLift (pinQuarterLift (pinQuarterLift psi))) = psi := by
  exact ⟨pinQuarterLift_sq psi, pinQuarterLift_four psi⟩

end GppKleinPinOrderFourBlock
