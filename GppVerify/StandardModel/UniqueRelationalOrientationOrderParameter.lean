import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# Uniqueness of the relational orientation order parameter

On the four microscopic lifts `(++,+-,-+,--)`, consider an arbitrary operator which is
diagonal in the lift basis,

    A = diag(a,b,c,d).

Impose exactly the discrete transformation law suggested by the physical programme:

1. `A` is EVEN under the complete diagonal reversal `D:(c,t)->(-c,-t)`;
2. `A` is ODD under one microscopic half flip (representation conjugacy alone).

Then the coefficients are forced to be

    (a,-a,-a,a),

so

    A = a chi,

where `chi=ct` is the relational alignment grading.  The other half flip is then
necessarily odd as well.

Thus, among observables/order parameters that are diagonal in the microscopic orientation
basis, the product character `ct` is not an arbitrary ansatz: it is the UNIQUE nontrivial
transformation law which is invariant under full reversal and changes sign under a half
reversal.

The qualifier "diagonal in the lift basis" matters.  Without it there are additional
matrix operators with the same abstract parity properties.  The theorem therefore applies
to a classical orientation label / grading, not to the most general quantum interaction.
-/

namespace GppUniqueRelationalOrientationOrderParameter

open GppFourOrientationGaugeProjection

/-- General operator diagonal in the microscopic lift basis. -/
def diagLiftOp (a b c d : ℂ) (v : Orientation4) : Orientation4 :=
  (a*v.1, b*v.2.1, c*v.2.2.1, d*v.2.2.2)

/-- Scalar multiple of the relational grading in tuple coordinates. -/
def chiScaled (a : ℂ) (v : Orientation4) : Orientation4 := a • chi v

/-- Full diagonal-reversal evenness forces opposite corners to agree. -/
theorem diag_even_forces_corner_pairing
    (a b c d : ℂ)
    (hD : ∀ v : Orientation4,
      diagReverse (diagLiftOp a b c d v) =
        diagLiftOp a b c d (diagReverse v)) :
    d = a ∧ c = b := by
  have h0 := hD ((1:ℂ),0,0,0)
  have h1 := hD ((0:ℂ),1,0,0)
  constructor
  · have hc := congrArg (fun v : Orientation4 => v.2.2.2) h0
    simpa [diagReverse, diagLiftOp] using hc
  · have hc := congrArg (fun v : Orientation4 => v.2.2.1) h1
    simpa [diagReverse, diagLiftOp] using hc

/-- Oddness under the representation half flip pairs the diagonal coefficients with
    opposite signs. -/
theorem charge_half_odd_forces_opposite_pairing
    (a b c d : ℂ)
    (hC : ∀ v : Orientation4,
      diagLiftOp a b c d (chargeFlip v) =
        - chargeFlip (diagLiftOp a b c d v)) :
    c = -a ∧ d = -b := by
  have h0 := hC ((1:ℂ),0,0,0)
  have h1 := hC ((0:ℂ),1,0,0)
  constructor
  · have hc := congrArg (fun v : Orientation4 => v.2.2.1) h0
    simpa [chargeFlip, diagLiftOp] using hc
  · have hc := congrArg (fun v : Orientation4 => v.2.2.2) h1
    simpa [chargeFlip, diagLiftOp] using hc

/-- Main uniqueness theorem: complete-reversal even + half-flip odd uniquely forces the
    relational character `chi`, up to one overall scalar normalization. -/
theorem unique_diagonal_order_parameter_is_chi
    (a b c d : ℂ)
    (hD : ∀ v : Orientation4,
      diagReverse (diagLiftOp a b c d v) =
        diagLiftOp a b c d (diagReverse v))
    (hC : ∀ v : Orientation4,
      diagLiftOp a b c d (chargeFlip v) =
        - chargeFlip (diagLiftOp a b c d v)) :
    ∀ v : Orientation4, diagLiftOp a b c d v = chiScaled a v := by
  obtain ⟨hda,hcb⟩ := diag_even_forces_corner_pairing a b c d hD
  obtain ⟨hca,hdb⟩ := charge_half_odd_forces_opposite_pairing a b c d hC
  have hba : b = -a := by rw [← hcb, hca]
  have hcc : c = -a := hca
  have hdd : d = a := hda
  intro v
  rcases v with ⟨x,y,z,w⟩
  subst b
  subst c
  subst d
  simp [diagLiftOp, chiScaled, chi]

/-- Once the unique form is imposed, the temporal half flip is automatically odd too. -/
theorem unique_form_is_temporal_half_odd (a : ℂ) (v : Orientation4) :
    chiScaled a (temporalFlip v) =
      - temporalFlip (chiScaled a v) := by
  rcases v with ⟨x,y,z,w⟩
  simp [chiScaled, chi, temporalFlip]

/-- And the full diagonal reversal is automatically even. -/
theorem unique_form_is_diagonal_even (a : ℂ) (v : Orientation4) :
    diagReverse (chiScaled a v) = chiScaled a (diagReverse v) := by
  rcases v with ⟨x,y,z,w⟩
  simp [chiScaled, chi, diagReverse]

end GppUniqueRelationalOrientationOrderParameter
