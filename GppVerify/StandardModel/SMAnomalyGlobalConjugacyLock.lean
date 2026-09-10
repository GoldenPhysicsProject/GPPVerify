import Mathlib.Tactic

/-!
# Standard-Model anomaly cancellation locks independent conjugacy flips globally

Take the five left-handed Weyl multiplet types of one Standard-Model generation,

    Q, u^c, d^c, L, e^c,

with their usual representation/hypercharge magnitudes.  Restrict attention to the discrete
family obtained by independently replacing any multiplet by its complete conjugate
representation.  Let one Boolean sign per multiplet record whether that conjugation has
been made.  Conjugation reverses the cubic non-Abelian anomaly coefficient and all odd
hypercharge anomaly contributions.

After clearing harmless common denominators, the anomaly coefficients are

    SU(3)^3      :  2 q - u - d,
    SU(3)^2 U(1) :  q - 2u + d,
    SU(2)^2 U(1) :  q - l,
    grav^2 U(1)  :  q - 2u + d - l + e,
    U(1)^3       :  q - 32u + 4d - 9l + 36e,

where each lowercase symbol is `+1` or `-1` multiplying the contribution of the standard
multiplet.

Exact finite exhaustion proves that simultaneous cancellation of these anomalies permits
only TWO sign patterns: all five multiplets in the standard orientation, or all five
conjugated together.  No isolated or partial representation-conjugacy flip survives.

This is a strong, but deliberately scoped, locking theorem.  It is NOT a classification of
all possible anomaly-free gauge theories or all possible hypercharge assignments.  It says
that, within the fixed Standard-Model multiplet content and fixed charge magnitudes, the
operation `R -> R*` is globally locked across the generation by anomaly cancellation.
-/

namespace GppSMAnomalyGlobalConjugacyLock

/-- Convert a conjugation bit to the sign multiplying the standard anomaly contribution. -/
def orientSign (b : Bool) : ℤ := if b then -1 else 1

/-- Cleared `SU(3)^3` anomaly coefficient. -/
def su3Cube (q u d : Bool) : ℤ :=
  2*orientSign q - orientSign u - orientSign d

/-- Cleared `SU(3)^2 U(1)` anomaly coefficient. -/
def su3SqY (q u d : Bool) : ℤ :=
  orientSign q - 2*orientSign u + orientSign d

/-- Cleared `SU(2)^2 U(1)` anomaly coefficient. -/
def su2SqY (q l : Bool) : ℤ := orientSign q - orientSign l

/-- Cleared mixed gravitational-hypercharge anomaly coefficient. -/
def gravY (q u d l e : Bool) : ℤ :=
  orientSign q - 2*orientSign u + orientSign d - orientSign l + orientSign e

/-- Cleared cubic-hypercharge anomaly coefficient (common denominator 36 removed). -/
def yCube (q u d l e : Bool) : ℤ :=
  orientSign q - 32*orientSign u + 4*orientSign d - 9*orientSign l + 36*orientSign e

/-- All local perturbative anomaly coefficients considered here vanish. -/
def AnomalyFree (q u d l e : Bool) : Prop :=
  su3Cube q u d = 0 ∧
  su3SqY q u d = 0 ∧
  su2SqY q l = 0 ∧
  gravY q u d l e = 0 ∧
  yCube q u d l e = 0

/-- Global conjugacy locking: anomaly cancellation is equivalent to all five conjugation
    bits agreeing. -/
theorem anomalyFree_iff_all_orientations_locked
    (q u d l e : Bool) :
    AnomalyFree q u d l e ↔ (q = u ∧ u = d ∧ d = l ∧ l = e) := by
  cases q <;> cases u <;> cases d <;> cases l <;> cases e <;>
    native_decide

/-- The ordinary Standard-Model orientation is anomaly free. -/
theorem standard_orientation_anomaly_free :
    AnomalyFree false false false false false := by
  native_decide

/-- Its complete conjugate is anomaly free as well. -/
theorem fully_conjugate_orientation_anomaly_free :
    AnomalyFree true true true true true := by
  native_decide

/-- Any anomaly-free assignment is either the standard orientation for every multiplet or
    the complete conjugate orientation for every multiplet. -/
theorem anomaly_free_has_only_two_global_choices
    (q u d l e : Bool) (h : AnomalyFree q u d l e) :
    (q = false ∧ u = false ∧ d = false ∧ l = false ∧ e = false) ∨
    (q = true ∧ u = true ∧ d = true ∧ l = true ∧ e = true) := by
  have hall := (anomalyFree_iff_all_orientations_locked q u d l e).1 h
  rcases hall with ⟨hqu,hud,hdl,hle⟩
  subst u
  subst d
  subst l
  subst e
  cases q <;> simp

/-- In particular, flipping exactly one multiplet out of an anomaly-free global orientation
    destroys anomaly cancellation. -/
theorem no_single_Q_conjugacy_flip :
    ¬ AnomalyFree true false false false false := by
  native_decide

/-- The locking already implies that the representation-conjugacy sign is a generation-wide
    datum inside this restricted family, rather than an independent per-multiplet bit. -/
theorem anomaly_free_Q_orientation_determines_all
    (q u d l e : Bool) (h : AnomalyFree q u d l e) :
    u = q ∧ d = q ∧ l = q ∧ e = q := by
  have hall := (anomalyFree_iff_all_orientations_locked q u d l e).1 h
  rcases hall with ⟨hqu,hud,hdl,hle⟩
  exact ⟨hqu.symm, (hqu.trans hud).symm,
    (hqu.trans (hud.trans hdl)).symm,
    (hqu.trans (hud.trans (hdl.trans hle))).symm⟩

end GppSMAnomalyGlobalConjugacyLock
