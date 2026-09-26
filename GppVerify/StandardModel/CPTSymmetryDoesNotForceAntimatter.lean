import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# Diagonal CPT symmetry does not force a matter/antimatter balance

On the four microscopic orientation lifts `(++,+-,-+,--)`, the diagonal reversal

    D : (++ <-> --), (+- <-> -+)

commutes with the relational grading `chi = q*t`.  Therefore imposing `D psi = psi`
constrains each relational sector internally but does not relate the `chi=+1` and `chi=-1`
sectors to one another.

This is the finite algebraic statement needed for the cosmological interpretation: a state
may be exactly invariant under the diagonal CPT/deck operation while lying entirely in the
relational matter sector.  Thus diagonal CPT symmetry alone does NOT require a 50/50
population of relational matter and relational antimatter.

The statement is not a claim that the physical CPT operator of the Standard Model has
already been identified with `D`.  It says what follows if the project's diagonal
orientation involution is the relevant global CPT/deck action.
-/

namespace GppCPTSymmetryDoesNotForceAntimatter

open GppFourOrientationGaugeProjection

/-- Every pair of independent matter/antimatter amplitudes gives a diagonal-even state. -/
theorem diagonal_symmetry_leaves_sector_amplitudes_independent (a b : ℂ) :
    diagReverse (physicalLift a b) = physicalLift a b := by
  rfl

/-- The relational grading acts only by changing the sign of the antimatter amplitude. -/
theorem relational_grading_on_diagonal_sector (a b : ℂ) :
    chi (physicalLift a b) = physicalLift a (-b) := by
  simp [chi, physicalLift]

/-- A nonzero pure matter state is exactly diagonal-CPT/deck invariant. -/
theorem pure_matter_is_diagonal_invariant :
    diagReverse matterLift = matterLift ∧
    chi matterLift = matterLift ∧
    matterLift ≠ (0 : Orientation4) := by
  refine ⟨basis_lifts_diag_even.1, chi_matter, ?_⟩
  intro h
  have h0 := congrArg (fun v : Orientation4 => v.1) h
  norm_num [matterLift] at h0

/-- Likewise a pure relational-antimatter state is diagonal invariant, but has the opposite
    `chi` eigenvalue.  Hence diagonal symmetry by itself cannot choose or balance them. -/
theorem pure_antimatter_is_diagonal_invariant :
    diagReverse antimatterLift = antimatterLift ∧
    chi antimatterLift = -antimatterLift ∧
    antimatterLift ≠ (0 : Orientation4) := by
  refine ⟨basis_lifts_diag_even.2, chi_antimatter, ?_⟩
  intro h
  have h0 := congrArg (fun v : Orientation4 => v.2.1) h
  norm_num [antimatterLift] at h0

/-- Main no-balance theorem: there exists an exactly diagonal-invariant nonzero state with
    `chi=+1`.  Therefore diagonal CPT/deck invariance does not logically imply any
    relational-antimatter component. -/
theorem diagonal_CPT_does_not_force_antimatter_balance :
    ∃ v : Orientation4,
      v ≠ 0 ∧ diagReverse v = v ∧ chi v = v := by
  exact ⟨matterLift, pure_matter_is_diagonal_invariant.2.2,
    pure_matter_is_diagonal_invariant.1,
    pure_matter_is_diagonal_invariant.2.1⟩

/-- Stronger separation statement: both opposite `chi` eigenvalues occur inside the same
    diagonal-even subspace. -/
theorem diagonal_even_sector_contains_both_relational_classes :
    (diagReverse matterLift = matterLift ∧ chi matterLift = matterLift) ∧
    (diagReverse antimatterLift = antimatterLift ∧
      chi antimatterLift = -antimatterLift) := by
  exact ⟨⟨basis_lifts_diag_even.1, chi_matter⟩,
    ⟨basis_lifts_diag_even.2, chi_antimatter⟩⟩

end GppCPTSymmetryDoesNotForceAntimatter
