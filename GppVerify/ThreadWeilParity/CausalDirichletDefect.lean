import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Causal shift Dirichlet defect identity

The CCM causal-shift realization repeatedly contains the Hermitian defect

  2 I - (V + V^*).

For any square matrix this splits algebraically into a difference square plus the
isometry defect:

  (I-V)^*(I-V) + (I-V^*V).

For the unilateral causal shifts used by the RH program, the second term is the
boundary-loss projection.  This is the exact Dirichlet/boundary decomposition behind
the non-pole Hodge form.

This file proves only the algebraic identity; positivity of a concrete isometry defect
is a separate operator-specific statement.
-/

open Matrix

namespace GppWeilParity

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem causal_dirichlet_defect_identity (V : Matrix n n ℂ) :
    (1 - V)ᴴ * (1 - V) + (1 - Vᴴ * V)
      = (1 : Matrix n n ℂ) + 1 - (V + Vᴴ) := by
  rw [conjTranspose_sub, conjTranspose_one]
  noncomm_ring

end GppWeilParity
