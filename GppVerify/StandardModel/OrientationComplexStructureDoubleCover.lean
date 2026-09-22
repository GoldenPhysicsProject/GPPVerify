import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# Two microscopic complex orientations on a diagonal double cover

This file gives the strongest finite realization yet of the proposed "two arrows, only
alignment is visible" picture.

On the four kinematic lifts (++,+-,-+,--) define two commuting complex structures

    I_q = i * diag(+,+,-,-),
    I_t = i * diag(+,-,+,-).

Each squares to `-1`.  Their relative product is

    - I_q I_t = diag(+,-,-,+) = χ,

exactly the relational matter/charge grading.

The simultaneous diagonal reversal `D` exchanges (++<->--) and (+-<->-+).  It
anticommutes with EACH microscopic complex structure separately,

    D I_q = - I_q D,
    D I_t = - I_t D,

but commutes with their product `χ`.  Therefore if `D` is imposed as a gauge/deck
constraint, neither microscopic arrow is separately an operator on the physical even
sector; each sends even states to odd states.  Their relative alignment, however, descends
perfectly and is observable.

This is precisely the algebraic architecture required by the current interpretation.  It
also sharpens the relation to standard charged-Kahler theory, where a physical charge
operator is `-ij` for two commuting complex structures.  The new/nonstandard ingredient
here is placing the two individual complex structures on a double cover while allowing
only their product to descend through a diagonal Z2 quotient.
-/

namespace GppOrientationComplexStructureDoubleCover

open GppFourOrientationGaugeProjection

/-- Microscopic gauge-orientation complex structure. -/
def Iq (v : Orientation4) : Orientation4 :=
  (Complex.I*v.1,
   Complex.I*v.2.1,
   -Complex.I*v.2.2.1,
   -Complex.I*v.2.2.2)

/-- Microscopic temporal/frequency-orientation complex structure. -/
def It (v : Orientation4) : Orientation4 :=
  (Complex.I*v.1,
   -Complex.I*v.2.1,
   Complex.I*v.2.2.1,
   -Complex.I*v.2.2.2)

/-- Both microscopic orientations are genuine complex structures. -/
theorem Iq_sq_neg (v : Orientation4) : Iq (Iq v) = -v := by
  rcases v with ⟨a,b,c,d⟩
  simp [Iq, Complex.I_mul_I]
  ring

 theorem It_sq_neg (v : Orientation4) : It (It v) = -v := by
  rcases v with ⟨a,b,c,d⟩
  simp [It, Complex.I_mul_I]
  ring

/-- The two microscopic complex structures commute. -/
theorem Iq_It_commute (v : Orientation4) :
    Iq (It v) = It (Iq v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [Iq, It, Complex.I_mul_I]
  ring

/-- Their relative product is exactly the observable alignment grading. -/
theorem minus_Iq_It_eq_chi (v : Orientation4) :
    - Iq (It v) = chi v := by
  rcases v with ⟨a,b,c,d⟩
  simp [Iq, It, chi, Complex.I_mul_I]
  ring

/-- Diagonal reversal flips the gauge complex orientation. -/
theorem diag_anticommutes_Iq (v : Orientation4) :
    diagReverse (Iq v) = - Iq (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagReverse, Iq]

/-- Diagonal reversal also flips the microscopic temporal complex orientation. -/
theorem diag_anticommutes_It (v : Orientation4) :
    diagReverse (It v) = - It (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagReverse, It]

/-- But the relative alignment survives the diagonal quotient. -/
theorem diag_commutes_relative_product (v : Orientation4) :
    diagReverse (-Iq (It v)) = -Iq (It (diagReverse v)) := by
  rw [minus_Iq_It_eq_chi, minus_Iq_It_eq_chi, diag_commutes_chi]

/-- On a diagonal-even candidate physical vector, either individual complex structure lands
in the odd sector. -/
theorem individual_arrows_do_not_descend
    (v : Orientation4) (h : diagReverse v = v) :
    diagReverse (Iq v) = -Iq v ∧
    diagReverse (It v) = -It v := by
  constructor
  · rw [diag_anticommutes_Iq, h]
  · rw [diag_anticommutes_It, h]

/-- Their product DOES descend and preserves the physical even sector. -/
theorem alignment_does_descend
    (v : Orientation4) (h : diagReverse v = v) :
    diagReverse (-Iq (It v)) = -Iq (It v) := by
  rw [minus_Iq_It_eq_chi]
  exact chi_preserves_even v h

/-- Simultaneously reversing the two microscopic complex structures changes neither their
relative product nor the physical grading. -/
theorem reverse_both_complex_orientations_preserves_alignment (v : Orientation4) :
    - ((fun x => -Iq x) ((fun x => -It x) v)) = chi v := by
  rw [minus_Iq_It_eq_chi]
  simp

/-- Capstone: physical matter/antimatter is alignment versus anti-alignment, while the two
microscopic arrows separately are gauge-odd under diagonal reversal. -/
theorem double_cover_alignment_capstone :
    (-Iq (It matterLift) = matterLift) ∧
    (-Iq (It antimatterLift) = -antimatterLift) ∧
    (diagReverse matterLift = matterLift) ∧
    (diagReverse antimatterLift = antimatterLift) := by
  rw [minus_Iq_It_eq_chi, minus_Iq_It_eq_chi]
  exact ⟨chi_matter, chi_antimatter, rfl, rfl⟩

end GppOrientationComplexStructureDoubleCover
