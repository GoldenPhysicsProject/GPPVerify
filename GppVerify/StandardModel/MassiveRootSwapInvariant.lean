import Mathlib.Tactic
import GppVerify.StandardModel.MassiveSpinorOrientationFlip

/-!
# The massive momentum is unordered while its spinor square root is oriented

For two complex two-spinors `u,v`, the positive Hermitian momentum assembled from their
rank-one projectors is

    p = u u^† + v v^†.

This sum is exactly invariant under exchanging the two roots.  By contrast the symplectic
area

    <u v> = u1 v2 - u2 v1

is antisymmetric and therefore changes sign.  Its norm is unchanged.

Hence a massive momentum naturally forgets an internal ordering/orientation of its two
null spinor roots:

    (u,v) and (v,u) -> same p,
    <v u> = -<u v>,
    |<v u>| = |<u v>|.

For the physical root pair already constructed in `MassOrientationCoupling`, the final
modulus is the mass.  This is a precise two-lift structure in the massive extension: an
orientation sign exists upstairs at the spinor-root level but is invisible to the
four-momentum and the positive mass downstairs.

No claim is made here that this hidden ordering is electric charge, particle/antiparticle,
or CPT.  Proving such a dictionary requires the gauge and discrete-symmetry action on the
root pair.
-/

namespace GppMassiveRootSwapInvariant

open scoped ComplexConjugate
open GppMassiveSpinorOrientationFlip

/-- `00` entry of `u u^† + v v^†`. -/
def momentum00 (u v : ℂ × ℂ) : ℂ :=
  u.1 * conj u.1 + v.1 * conj v.1

/-- `01` entry of `u u^† + v v^†`. -/
def momentum01 (u v : ℂ × ℂ) : ℂ :=
  u.1 * conj u.2 + v.1 * conj v.2

/-- `10` entry, written explicitly rather than inferred by Hermiticity. -/
def momentum10 (u v : ℂ × ℂ) : ℂ :=
  u.2 * conj u.1 + v.2 * conj v.1

/-- `11` entry of `u u^† + v v^†`. -/
def momentum11 (u v : ℂ × ℂ) : ℂ :=
  u.2 * conj u.2 + v.2 * conj v.2

/-- Every momentum component is exactly invariant under root exchange. -/
theorem momentum_entries_swap_invariant (u v : ℂ × ℂ) :
    momentum00 v u = momentum00 u v ∧
    momentum01 v u = momentum01 u v ∧
    momentum10 v u = momentum10 u v ∧
    momentum11 v u = momentum11 u v := by
  constructor
  · simp [momentum00, add_comm]
  · constructor
    · simp [momentum01, add_comm]
    · constructor
      · simp [momentum10, add_comm]
      · simp [momentum11, add_comm]

/-- Root exchange reverses only the oriented spinor area, not its invariant modulus. -/
theorem root_swap_orientation_capstone (u v : ℂ × ℂ) :
    momentum00 v u = momentum00 u v ∧
    momentum01 v u = momentum01 u v ∧
    momentum10 v u = momentum10 u v ∧
    momentum11 v u = momentum11 u v ∧
    orderedSpinorArea v u = - orderedSpinorArea u v ∧
    ‖orderedSpinorArea v u‖ = ‖orderedSpinorArea u v‖ := by
  rcases momentum_entries_swap_invariant u v with ⟨h00,h01,h10,h11⟩
  exact ⟨h00,h01,h10,h11,
    orderedSpinorArea_swap u v,
    orderedSpinorArea_norm_swap u v⟩

end GppMassiveRootSwapInvariant
