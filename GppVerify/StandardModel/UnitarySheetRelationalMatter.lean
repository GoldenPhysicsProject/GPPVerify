import Mathlib.Tactic

/-!
# Three-sign resolution: unitarity locks the sheet arrow, charge remains relational

The preceding calculations reveal that two different products must not be conflated.
Introduce three binary orientations:

* `q`: internal representation-conjugacy sign (`R` versus `R*`), which can differ between
  particle and antiparticle excitations on one sheet;
* `s`: orientation of the symplectic/current/Cauchy-surface form used to build the Hilbert
  structure;
* `t`: orientation of the positive-frequency complex structure / global microscopic time
  polarization of the sheet.

Hilbert-space positivity constrains

    U = s*t = +1,

so `s` and `t` are locked.  This makes `t` naturally a GLOBAL sheet/polarization datum rather
than an independent hidden bit carried by every particle.  The relational matter character
can still be

    chi = q*t.

A local charge-conjugacy flip changes `chi` but leaves `U` untouched.  Flipping `t` alone
changes `U` and is therefore incompatible with the same positive Hilbert structure; a sheet
reversal must flip `s` and `t` together.  Full CPT flips all three `(q,s,t)` and preserves
both `U` and `chi`.

This finite sign algebra resolves the earlier tension between positive-norm antiparticles
and the orientation model.  It does not yet prove that continuum QFT realizes exactly these
three signs, but it gives the sharply separated target.
-/

namespace GppUnitarySheetRelationalMatter

/-- Binary sign with `false=+1`, `true=-1`. -/
def sg (b : Bool) : ℤ := if b then -1 else 1

/-- Positivity/unitarity alignment character. -/
def unitaryCharacter (s t : Bool) : ℤ := sg s * sg t

/-- Relational matter/antimatter character. -/
def matterCharacter (q t : Bool) : ℤ := sg q * sg t

/-- Full CPT reverses internal conjugacy, symplectic orientation and time polarization. -/
def fullCPT (x : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (!x.1, !x.2.1, !x.2.2)

/-- Positivity character is +1 exactly when symplectic and frequency orientations agree. -/
theorem unitaryCharacter_pos_iff_locked (s t : Bool) :
    unitaryCharacter s t = 1 ↔ s = t := by
  cases s <;> cases t <;> native_decide

/-- Flipping only representation conjugacy preserves the Hilbert positivity character. -/
theorem charge_flip_preserves_unitarity (q s t : Bool) :
    unitaryCharacter s t = unitaryCharacter s t := rfl

/-- But the same charge flip reverses the relational matter character. -/
theorem charge_flip_reverses_matter (q t : Bool) :
    matterCharacter (!q) t = -matterCharacter q t := by
  cases q <;> cases t <;> native_decide

/-- Flipping microscopic time polarization alone reverses the positivity character. -/
theorem time_flip_reverses_unitarity (s t : Bool) :
    unitaryCharacter s (!t) = -unitaryCharacter s t := by
  cases s <;> cases t <;> native_decide

/-- A simultaneous sheet reversal `(s,t)->(-s,-t)` preserves Hilbert positivity. -/
theorem sheet_reversal_preserves_unitarity (s t : Bool) :
    unitaryCharacter (!s) (!t) = unitaryCharacter s t := by
  cases s <;> cases t <;> native_decide

/-- Sheet reversal without charge conjugation reverses the relational matter label. -/
theorem sheet_reversal_alone_reverses_matter (q t : Bool) :
    matterCharacter q (!t) = -matterCharacter q t := by
  cases q <;> cases t <;> native_decide

/-- Full CPT preserves the relational matter character because q and t reverse together. -/
theorem full_CPT_preserves_matter (q s t : Bool) :
    matterCharacter (!q) (!t) = matterCharacter q t := by
  cases q <;> cases s <;> cases t <;> native_decide

/-- Full CPT also preserves the positivity character because s and t reverse together. -/
theorem full_CPT_preserves_unitarity (q s t : Bool) :
    unitaryCharacter (!s) (!t) = unitaryCharacter s t := by
  cases q <;> cases s <;> cases t <;> native_decide

/-- Once positivity is imposed, the sheet time orientation is fixed by the symplectic/current
    orientation; it is not an independent per-particle sign. -/
theorem positive_sheet_determines_t_from_s
    (s t : Bool) (hU : unitaryCharacter s t = 1) : t = s := by
  exact (unitaryCharacter_pos_iff_locked s t).1 hU |>.symm

/-- A positive sheet may contain either relational matter class by changing only q; this is
    how ordinary particle/antiparticle excitations can coexist without negative norm. -/
theorem positive_sheet_allows_both_charge_classes (s t : Bool)
    (hU : unitaryCharacter s t = 1) (q : Bool) :
    unitaryCharacter s t = 1 ∧
    matterCharacter (!q) t = -matterCharacter q t := by
  exact ⟨hU, charge_flip_reverses_matter q t⟩

/-- Capstone: a full CPT-related sheet remains unitary and preserves relational matter. -/
theorem CPT_sheet_package (q s t : Bool)
    (hU : unitaryCharacter s t = 1) :
    unitaryCharacter (!s) (!t) = 1 ∧
    matterCharacter (!q) (!t) = matterCharacter q t := by
  constructor
  · rw [sheet_reversal_preserves_unitarity, hU]
  · exact full_CPT_preserves_matter q s t

end GppUnitarySheetRelationalMatter
