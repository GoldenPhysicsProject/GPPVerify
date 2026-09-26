import Mathlib.Tactic
import GppVerify.CelestialHolography.SturmReciprocalPotential

/-!
# Weyl-spinor bidegrees and the representation-theoretic googly exchange

For the complexified four-dimensional spin group

    Spin(4,C) = SL(2)_L x SL(2)_R,

a left Weyl spinor carries bidegree `(1,0)` and a right Weyl spinor `(0,1)`.
The two chiral Weyl-curvature spinors therefore have representation weights

    Psi_{ABCD}             : (4,0),
    Psitilde_{A'B'C'D'}    : (0,4),

while the trace-free Ricci spinor has mixed weight `(2,2)`.

The canonical factor exchange `(p,q)->(q,p)` consequently swaps the two Weyl-curvature
representations and fixes the mixed Ricci representation.  In helicity language, if twice
the helicity is the weight difference `p-q`, the same exchange sends `+4` to `-4`, i.e.
spin-two helicity `+2` to `-2`.

This is the exact representation-theoretic core a curved googly reconstruction must carry.
It does not prove that a particular ambitwistor/Penrose transform reconstructs the two
Weyl spinors from one contact geometry; it proves that *if* the two `SL(2)` factors of the
contact/ruling geometry are the spacetime half-spin factors, then factor exchange has
exactly the required action on the full Einstein curvature representations.
-/

namespace GppSpinorWeylBidegreeGoogly

open GppAmbitwistorSturmBidegrees
open GppSturmReciprocalPotential

/-- Fundamental half-spin representation weights. -/
def leftSpinorWeight : BiWeight := (1,0)
def rightSpinorWeight : BiWeight := (0,1)

/-- Chiral Weyl-curvature and trace-free Ricci spinor weights. -/
def plusWeylWeight : BiWeight := (4,0)
def minusWeylWeight : BiWeight := (0,4)
def tracefreeRicciWeight : BiWeight := (2,2)
def scalarCurvatureWeight : BiWeight := (0,0)

/-- Factor exchange swaps the two fundamental half-spin representations. -/
theorem factorSwap_halfSpin :
    swapBiWeight leftSpinorWeight = rightSpinorWeight ∧
    swapBiWeight rightSpinorWeight = leftSpinorWeight := by
  norm_num [swapBiWeight, leftSpinorWeight, rightSpinorWeight]

/-- Main representation-theoretic googly statement: the two Weyl spinors are exchanged. -/
theorem factorSwap_Weyl :
    swapBiWeight plusWeylWeight = minusWeylWeight ∧
    swapBiWeight minusWeylWeight = plusWeylWeight := by
  norm_num [swapBiWeight, plusWeylWeight, minusWeylWeight]

/-- The mixed trace-free-Ricci representation is fixed by factor exchange. -/
theorem factorSwap_tracefreeRicci :
    swapBiWeight tracefreeRicciWeight = tracefreeRicciWeight := by
  norm_num [swapBiWeight, tracefreeRicciWeight]

/-- The scalar-curvature representation is also fixed. -/
theorem factorSwap_scalar :
    swapBiWeight scalarCurvatureWeight = scalarCurvatureWeight := by
  norm_num [swapBiWeight, scalarCurvatureWeight]

/-- Twice-helicity is the difference of the two half-spin homogeneities. -/
def twiceHelicity (w : BiWeight) : ℤ := w.1 - w.2

/-- The two Weyl spinors carry opposite spin-two helicities. -/
theorem Weyl_twiceHelicity :
    twiceHelicity plusWeylWeight = 4 ∧
    twiceHelicity minusWeylWeight = -4 := by
  norm_num [twiceHelicity, plusWeylWeight, minusWeylWeight]

/-- Factor exchange reverses twice-helicity for every bidegree. -/
theorem factorSwap_reverses_twiceHelicity (w : BiWeight) :
    twiceHelicity (swapBiWeight w) = - twiceHelicity w := by
  rcases w with ⟨p,q⟩
  simp [twiceHelicity, swapBiWeight]
  ring

/-- The mixed Ricci representation has zero helicity and is therefore not the googly pair. -/
theorem tracefreeRicci_zero_helicity :
    twiceHelicity tracefreeRicciWeight = 0 := by
  norm_num [twiceHelicity, tracefreeRicciWeight]

/-- In vacuum Einstein representation content, removing the mixed Ricci block leaves a
pair which factor exchange acts on exactly as the googly/helicity involution. -/
theorem vacuum_pair_is_factor_exchange_pair :
    swapBiWeight plusWeylWeight = minusWeylWeight ∧
    swapBiWeight minusWeylWeight = plusWeylWeight ∧
    twiceHelicity plusWeylWeight = 4 ∧
    twiceHelicity minusWeylWeight = -4 := by
  norm_num [swapBiWeight, plusWeylWeight, minusWeylWeight, twiceHelicity]

end GppSpinorWeylBidegreeGoogly
