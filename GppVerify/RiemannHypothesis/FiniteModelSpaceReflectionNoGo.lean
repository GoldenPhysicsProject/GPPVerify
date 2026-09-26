import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite model-space reflection no-go

A reflection which exchanges a compressed forward shift with its backward/adjoint partner
does **not** force the defect space to vanish.  This is the finite algebraic skeleton of the
canonical conjugation carried by every Hardy model space `K_B`.

The carrier below is deliberately only two-dimensional.  It proves the exact point needed
for the RH program:

* a nonzero state space can carry an involutive reflection `J`;
* `J` exchanges forward and backward nilpotent shifts;
* the two rank-one boundary defects are exchanged by the same reflection;
* those defects are nevertheless nonzero.

Thus quotient-level reflection symmetry is too weak to eliminate the Nyman--Burnol ghost
space.  A proof of RH must instead annihilate the boundary defect (or lift the symmetry to
the ambient causal Hardy dynamics).  No claim is made here that this finite carrier is the
actual Nyman model space.
-/

namespace GppFiniteModelSpaceReflectionNoGo

abbrev State := ℂ × ℂ

/-- Two-step forward compressed shift. -/
def forward (u : State) : State := (0, u.1)

/-- Backward partner of `forward`. -/
def backward (u : State) : State := (u.2, 0)

/-- Reflection exchanging the two defect directions. -/
def reflect (u : State) : State := (u.2, u.1)

/-- Incoming rank-one defect. -/
def incomingDefect (u : State) : State := (u.1, 0)

/-- Outgoing rank-one defect. -/
def outgoingDefect (u : State) : State := (0, u.2)

@[simp] theorem reflect_involutive (u : State) :
    reflect (reflect u) = u := by
  rcases u with ⟨x, y⟩
  rfl

@[simp] theorem forward_sq_zero (u : State) :
    forward (forward u) = (0, 0) := by
  rcases u with ⟨x, y⟩
  rfl

@[simp] theorem backward_sq_zero (u : State) :
    backward (backward u) = (0, 0) := by
  rcases u with ⟨x, y⟩
  rfl

/-- Exact reflected forward/backward symmetry on a nontrivial carrier. -/
theorem reflect_forward_reflect_eq_backward (u : State) :
    reflect (forward (reflect u)) = backward u := by
  rcases u with ⟨x, y⟩
  rfl

/-- The reverse conjugacy holds as well. -/
theorem reflect_backward_reflect_eq_forward (u : State) :
    reflect (backward (reflect u)) = forward u := by
  rcases u with ⟨x, y⟩
  rfl

/-- Failure of coisometry is precisely the incoming rank-one defect. -/
theorem incoming_defect_identity (u : State) :
    u - forward (backward u) = incomingDefect u := by
  rcases u with ⟨x, y⟩
  simp [forward, backward, incomingDefect]

/-- Failure of isometry is precisely the outgoing rank-one defect. -/
theorem outgoing_defect_identity (u : State) :
    u - backward (forward u) = outgoingDefect u := by
  rcases u with ⟨x, y⟩
  simp [forward, backward, outgoingDefect]

/-- Reflection swaps the two boundary defects rather than removing them. -/
theorem reflect_incoming_eq_outgoing_reflect (u : State) :
    reflect (incomingDefect u) = outgoingDefect (reflect u) := by
  rcases u with ⟨x, y⟩
  rfl

/-- Reflection swaps the two boundary defects in the opposite direction too. -/
theorem reflect_outgoing_eq_incoming_reflect (u : State) :
    reflect (outgoingDefect u) = incomingDefect (reflect u) := by
  rcases u with ⟨x, y⟩
  rfl

/-- The reflected system still has a genuinely nonzero incoming defect. -/
theorem incoming_defect_nonzero :
    incomingDefect ((1 : ℂ), 0) ≠ (0, 0) := by
  norm_num [incomingDefect]

/-- The reflected system still has a genuinely nonzero outgoing defect. -/
theorem outgoing_defect_nonzero :
    outgoingDefect (0, (1 : ℂ)) ≠ (0, 0) := by
  norm_num [outgoingDefect]

/--
Finite no-go: involutive reflected forward/backward symmetry and nonzero rank-one boundary
defect coexist exactly.  Therefore reflection symmetry alone cannot imply ghost-sector
vanishing.
-/
theorem reflection_symmetry_does_not_force_zero_defect :
    (∀ u : State, reflect (forward (reflect u)) = backward u) ∧
    incomingDefect ((1 : ℂ), 0) ≠ (0, 0) := by
  constructor
  · exact reflect_forward_reflect_eq_backward
  · exact incoming_defect_nonzero

end GppFiniteModelSpaceReflectionNoGo
