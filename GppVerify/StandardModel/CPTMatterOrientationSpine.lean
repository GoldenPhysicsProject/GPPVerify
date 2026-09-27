import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime
import GppVerify.StandardModel.HalfFlipProposition
import GppVerify.QuantumInformation.TransposeNotCompletelyPositive

/-!
# CPT matter-orientation spine: full flip, half flip, and local no-enactment

The current orientation program needs three logically different statements kept separate.

1. **Relational orientation.**  At the finite sign level a state carries a charge/orientation
   sign and a time-orientation sign.  The simultaneous diagonal flip changes both, while
   the relational character `xor` is unchanged.  Thus the quotient by the diagonal flip has
   exactly two classes, and a full `(q,t)->(!q,!t)` flip stays in the same relational class.

2. **Half flips.**  Flipping only one sign changes that relational class.  This is the
   algebraic reason a charge flip at fixed laboratory time orientation is physically
   distinguishable from the full diagonal flip.

3. **Antiunitary no-enactment.**  On a Hermitian density matrix antiunitary conjugation
   contains a transpose.  For a qubit the transpose map is not completely positive, so the
   antiunitary core cannot be an arbitrary local quantum channel on an unknown subsystem.

Together these facts support a precise research distinction: a *global* CPT-related sector
may lie in the same relational orientation orbit even though a *local* antiparticle
operation at fixed time orientation is a different half-flip operation.  The theorems do
NOT prove that the observed cosmological baryon asymmetry is thereby explained, and they do
NOT identify gauge charge with the Boolean sign model without an additional representation
bridge.
-/

namespace GppCPTMatterOrientationSpine

open GppOrientationMassTime

/-- A full diagonal sign flip leaves the relational matter-orientation class invariant. -/
theorem full_flip_preserves_relational_class (x : Bool × Bool) :
    xorCharacter (diagFlip x) = xorCharacter x :=
  xorCharacter_diagFlip x

/-- Equality of relational classes means precisely equality or membership in the full
flip orbit. -/
theorem same_class_iff_same_or_full_flip (x y : Bool × Bool) :
    xorCharacter x = xorCharacter y ↔ y = x ∨ y = diagFlip x :=
  xorCharacter_eq_iff_diagOrbit x y

/-- Either single half-flip changes the relational class. -/
theorem either_half_flip_changes_class (q t : Bool) :
    xor (!q) t = !(xor q t) ∧ xor q (!t) = !(xor q t) :=
  finite_half_flip_changes_class q t

/-- The two possible single half-flips land in the same opposite relational class. -/
theorem two_half_flips_same_opposite_class (q t : Bool) :
    xor (!q) t = xor q (!t) :=
  finite_two_half_flips_agree q t

/-- Qubit Wigner time reversal has the spinorial central sign `T^2=-1`. -/
theorem wigner_time_reversal_sq_central_sign (psi1 psi2 : ℂ) :
    GppHalfFlip.wignerT
      (GppHalfFlip.wignerT psi1 psi2).1
      (GppHalfFlip.wignerT psi1 psi2).2 = (-psi1,-psi2) :=
  GppHalfFlip.wignerT_wignerT psi1 psi2

/-- The transpose core of antiunitary conjugation is not a completely positive qubit
channel.  This is the exact local no-enactment obstruction used by the half-flip program. -/
theorem transpose_core_not_completelyPositive :
    ¬ GppChoiMatrix.CompletelyPositive GppHalfFlipMatrix.transposeMap :=
  GppHalfFlipMatrix.transposeMap_not_completelyPositive

end GppCPTMatterOrientationSpine
