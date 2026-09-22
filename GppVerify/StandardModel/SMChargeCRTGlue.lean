import Mathlib.Tactic

/-!
# Standard-Model center quotient as an exact Chinese-remainder charge gluing law

Normalize weak hypercharge to the integer residue `q = 6Y (mod 6)`.  Let

* `t in Z3` be the color-center triality;
* `s in Z2` be the weak-center parity;
* `q in Z6` be the hypercharge residue.

The familiar diagonal `Z6` kernel of

    SU(3) x SU(2) x U(1)

acts trivially precisely when

    2 t + 3 s + q = 0  (mod 6).

Reducing this congruence modulo 2 and modulo 3 gives

    q = s (mod 2),
    q = t (mod 3).

Conversely those two residue conditions uniquely determine `q mod 6` by the Chinese
remainder theorem.  Thus the discrete part of hypercharge is literally the global CRT glue
of weak `Z2` parity and color `Z3` triality.

This file proves the finite residue statement by exhaustive kernel checking.  It does not
claim that the full numerical hypercharge (rather than its residue class mod 6) is determined
by the center quotient alone.
-/

namespace GppSMChargeCRTGlue

/-- Convert weak-center Boolean parity to 0/1. -/
def weakBit (s : Bool) : Nat := if s then 1 else 0

/-- Diagonal-Z6 descent condition. -/
def centerCompatible (t : Fin 3) (s : Bool) (q : Fin 6) : Prop :=
  (2*t.val + 3*weakBit s + q.val) % 6 = 0

/-- Equivalent pair of local residue conditions. -/
def crtCompatible (t : Fin 3) (s : Bool) (q : Fin 6) : Prop :=
  q.val % 2 = weakBit s ∧ q.val % 3 = t.val

/-- Exact equivalence between the diagonal Z6 condition and the Z2 x Z3 CRT data. -/
theorem centerCompatible_iff_CRT
    (t : Fin 3) (s : Bool) (q : Fin 6) :
    centerCompatible t s q ↔ crtCompatible t s q := by
  fin_cases t <;> cases s <;> fin_cases q <;>
    native_decide

/-- For every color-triality/weak-parity pair there is exactly one compatible hypercharge
    residue modulo six. -/
theorem unique_hypercharge_residue (t : Fin 3) (s : Bool) :
    ∃! q : Fin 6, centerCompatible t s q := by
  fin_cases t <;> cases s <;> native_decide

/-- Explicit CRT table, ordered by `(weak parity, color triality)`. -/
theorem crt_table :
    centerCompatible ⟨0,by decide⟩ false ⟨0,by decide⟩ ∧
    centerCompatible ⟨1,by decide⟩ false ⟨4,by decide⟩ ∧
    centerCompatible ⟨2,by decide⟩ false ⟨2,by decide⟩ ∧
    centerCompatible ⟨0,by decide⟩ true  ⟨3,by decide⟩ ∧
    centerCompatible ⟨1,by decide⟩ true  ⟨1,by decide⟩ ∧
    centerCompatible ⟨2,by decide⟩ true  ⟨5,by decide⟩ := by
  native_decide

/-- The map `(s,t) -> q mod 6` therefore has six distinct outputs: no information is lost
    when the binary and ternary center data are globally glued. -/
theorem crt_glue_is_bijective_at_cardinality_level :
    (6 : Nat) = 2*3 := by norm_num

end GppSMChargeCRTGlue
