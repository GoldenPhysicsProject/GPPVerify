import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-!
# Twistor flag duality by annihilators

The Penrose correspondence is built from flags `ell <= W` in a four-dimensional
vector space: a projective twistor point lies on a projective twistor line.
Annihilator duality reverses this incidence exactly:

  ell <= W  ==>  W^0 <= ell^0.

The reverse operation is dual coannihilation.  For vector spaces Mathlib proves
`W.dualAnnihilator.dualCoannihilator = W`, so the flag correspondence closes
exactly at the level of linear incidence geometry.  This is the algebraic core
needed before attempting a cohomological Penrose/googly pull-push transform.
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

/-- Dual coannihilator also reverses inclusion. -/
theorem dualCoannihilator_antitone
    {Phi Psi : Submodule K (Module.Dual K V)} (h : Phi ≤ Psi) :
    Psi.dualCoannihilator ≤ Phi.dualCoannihilator := by
  intro x hx
  rw [Submodule.mem_dualCoannihilator] at hx ⊢
  intro phi hphi
  exact hx phi (h hphi)

/-- The incidence datum used by the ordinary Penrose correspondence, stripped to
its linear-algebra core: a subspace `line` included in a subspace `plane`. -/
structure Flag12 where
  line : Submodule K V
  plane : Submodule K V
  incidence : line ≤ plane

/-- The annihilator-dual incidence datum. -/
structure DualFlag23 where
  planeAnn : Submodule K (Module.Dual K V)
  lineAnn : Submodule K (Module.Dual K V)
  incidence : planeAnn ≤ lineAnn

/-- Canonical annihilator map from an ordinary incidence flag to the reversed dual flag. -/
def annihilatorFlag (F : Flag12 (K:=K) (V:=V)) : DualFlag23 (K:=K) (V:=V) where
  planeAnn := F.plane.dualAnnihilator
  lineAnn := F.line.dualAnnihilator
  incidence := dualAnnihilator_antitone F.incidence

/-- Canonical reverse map by dual coannihilators. -/
def recoverFlag (F : DualFlag23 (K:=K) (V:=V)) : Flag12 (K:=K) (V:=V) where
  line := F.lineAnn.dualCoannihilator
  plane := F.planeAnn.dualCoannihilator
  incidence := dualCoannihilator_antitone F.incidence

/-- The defining incidence relation of the dual flag is forced by the original incidence. -/
theorem annihilatorFlag_incidence (F : Flag12 (K:=K) (V:=V)) :
    (annihilatorFlag F).planeAnn ≤ (annihilatorFlag F).lineAnn :=
  (annihilatorFlag F).incidence

/-- The annihilator/coannihilator round trip recovers the original Penrose flag exactly. -/
theorem recover_annihilatorFlag (F : Flag12 (K:=K) (V:=V)) :
    recoverFlag (annihilatorFlag F) = F := by
  cases F with
  | mk line plane incidence =>
      simp [recoverFlag, annihilatorFlag]

/-- In particular, annihilator flag duality is injective: no incidence data are lost. -/
theorem annihilatorFlag_injective :
    Function.Injective (annihilatorFlag : Flag12 (K:=K) (V:=V) → DualFlag23 (K:=K) (V:=V)) := by
  intro F G h
  have := congrArg recoverFlag h
  simpa [recover_annihilatorFlag] using this

section FourDimensional

variable [FiniteDimensional K V]

/-- In a four-dimensional vector space, the annihilator of a 2-plane is again
2-dimensional. -/
theorem plane_annihilator_finrank_two
    (W : Submodule K V) (hV : finrank K V = 4) (hW : finrank K W = 2) :
    finrank K W.dualAnnihilator = 2 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

/-- In a four-dimensional vector space, the annihilator of a line is a 3-plane. -/
theorem line_annihilator_finrank_three
    (L : Submodule K V) (hV : finrank K V = 4) (hL : finrank K L = 1) :
    finrank K L.dualAnnihilator = 3 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  omega

/-- Therefore a genuine `(1,2)` Penrose incidence flag in dimension four becomes
exactly a `(2,3)` dual flag under annihilator reversal. -/
theorem annihilatorFlag_dimensions
    (F : Flag12 (K:=K) (V:=V))
    (hV : finrank K V = 4)
    (hline : finrank K F.line = 1)
    (hplane : finrank K F.plane = 2) :
    finrank K (annihilatorFlag F).planeAnn = 2 ∧
    finrank K (annihilatorFlag F).lineAnn = 3 := by
  exact ⟨plane_annihilator_finrank_two F.plane hV hplane,
         line_annihilator_finrank_three F.line hV hline⟩

end FourDimensional

end GppTwistorFlagDuality
