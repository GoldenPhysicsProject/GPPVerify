import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic

/-!
# Twistor flag duality by annihilators

The Penrose correspondence is built from flags `ell <= W` in a four-dimensional
vector space: a projective twistor point lies on a projective twistor line.
Annihilator duality reverses this incidence exactly:

  ell <= W  ==>  W^0 <= ell^0.

This is the abstract linear-algebra statement behind the explicit big-cell computation
in `TwistorAnnihilatorIncidence.lean`.  It needs no coordinates and no twistor-specific
axiom; it is simply the antitonicity of the dual annihilator.
-/

namespace GppTwistorFlagDuality

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Dual annihilator reverses inclusion. -/
theorem dualAnnihilator_antitone {L W : Submodule K V} (hLW : L ≤ W) :
    W.dualAnnihilator ≤ L.dualAnnihilator := by
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ ⊢
  intro x hx
  exact hφ x (hLW hx)

/-- The incidence datum used by the ordinary Penrose correspondence, stripped to
its linear-algebra core: a subspace `line` included in a subspace `plane`.  Dimension
conditions (1 and 2 over C in the physical application) are deliberately separate. -/
structure Flag12 where
  line : Submodule K V
  plane : Submodule K V
  incidence : line ≤ plane

/-- The annihilator-dual incidence datum: the plane annihilator lies inside the
line annihilator.  In finite dimension four, a genuine `(1,2)` flag becomes a
`(2,3)` flag in the dual vector space. -/
structure DualFlag23 where
  planeAnn : Submodule K (Module.Dual K V)
  lineAnn : Submodule K (Module.Dual K V)
  incidence : planeAnn ≤ lineAnn

/-- Canonical annihilator map from an ordinary incidence flag to the reversed dual flag. -/
def annihilatorFlag (F : Flag12 (K:=K) (V:=V)) : DualFlag23 (K:=K) (V:=V) where
  planeAnn := F.plane.dualAnnihilator
  lineAnn := F.line.dualAnnihilator
  incidence := dualAnnihilator_antitone F.incidence

/-- The defining incidence relation of the dual flag is therefore not an added
hypothesis: it is forced by the original incidence. -/
theorem annihilatorFlag_incidence (F : Flag12 (K:=K) (V:=V)) :
    (annihilatorFlag F).planeAnn ≤ (annihilatorFlag F).lineAnn :=
  (annihilatorFlag F).incidence

end GppTwistorFlagDuality
