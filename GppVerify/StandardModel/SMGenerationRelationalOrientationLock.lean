import Mathlib.Tactic
import GppVerify.StandardModel.SMAnomalyGlobalConjugacyLock
import GppVerify.StandardModel.UnitarySheetRelationalMatter

/-!
# One anomaly-free Standard-Model generation carries one global conjugacy orientation

Combine two exact finite results:

1. anomaly cancellation locks the five Standard-Model Weyl multiplet conjugacy bits
   `Q,u^c,d^c,L,e^c` to one common value inside the fixed-magnitude conjugation family;
2. the relational matter character on a sheet is `chi = q*t`, where `t` is the global
   sheet/polarization orientation fixed by the Hilbert structure.

It follows that if ONE multiplet in an anomaly-free generation is aligned with the sheet,
then all five are aligned.  A complete CPT transformation flips every conjugacy bit and the
sheet orientation together, preserving all five relational matter characters and preserving
anomaly cancellation.

This gives an exact sense in which "matter orientation" is generation-wide rather than a
collection of independently chosen particle labels.  The theorem remains scoped to the
Standard-Model representation/sign family encoded in `SMAnomalyGlobalConjugacyLock`.
-/

namespace GppSMGenerationRelationalOrientationLock

open GppSMAnomalyGlobalConjugacyLock
open GppUnitarySheetRelationalMatter

/-- In an anomaly-free generation, one multiplet's relational orientation fixes all five. -/
theorem one_matter_orientation_fixes_generation
    (q u d l e t : Bool)
    (hA : AnomalyFree q u d l e)
    (hQ : matterCharacter q t = 1) :
    matterCharacter u t = 1 ∧
    matterCharacter d t = 1 ∧
    matterCharacter l t = 1 ∧
    matterCharacter e t = 1 := by
  obtain ⟨hu,hD,hL,hE⟩ := anomaly_free_Q_orientation_determines_all q u d l e hA
  subst u
  subst d
  subst l
  subst e
  exact ⟨hQ,hQ,hQ,hQ⟩

/-- Full conjugation of every multiplet preserves anomaly freedom. -/
theorem full_conjugation_preserves_anomaly_freedom
    (q u d l e : Bool) (hA : AnomalyFree q u d l e) :
    AnomalyFree (!q) (!u) (!d) (!l) (!e) := by
  have hall := (anomalyFree_iff_all_orientations_locked q u d l e).1 hA
  rcases hall with ⟨hqu,hud,hdl,hle⟩
  apply (anomalyFree_iff_all_orientations_locked (!q) (!u) (!d) (!l) (!e)).2
  simp only [Bool.not_eq_not]
  exact ⟨hqu,hud,hdl,hle⟩

/-- CPT reversal preserves the relational matter sign of every multiplet. -/
theorem full_CPT_preserves_generation_characters
    (q u d l e t : Bool) :
    matterCharacter (!q) (!t) = matterCharacter q t ∧
    matterCharacter (!u) (!t) = matterCharacter u t ∧
    matterCharacter (!d) (!t) = matterCharacter d t ∧
    matterCharacter (!l) (!t) = matterCharacter l t ∧
    matterCharacter (!e) (!t) = matterCharacter e t := by
  repeat' apply And.intro
  all_goals cases q <;> cases u <;> cases d <;> cases l <;> cases e <;> cases t <;> native_decide

/-- Capstone: an anomaly-free relational-matter generation maps under full CPT to another
    anomaly-free sheet presentation with the same relational matter class. -/
theorem anomaly_free_matter_generation_CPT_closed
    (q u d l e t : Bool)
    (hA : AnomalyFree q u d l e)
    (hQ : matterCharacter q t = 1) :
    AnomalyFree (!q) (!u) (!d) (!l) (!e) ∧
    matterCharacter (!q) (!t) = 1 ∧
    matterCharacter (!u) (!t) = 1 ∧
    matterCharacter (!d) (!t) = 1 ∧
    matterCharacter (!l) (!t) = 1 ∧
    matterCharacter (!e) (!t) = 1 := by
  have hgen := one_matter_orientation_fixes_generation q u d l e t hA hQ
  rcases hgen with ⟨hu,hd,hl,he⟩
  refine ⟨full_conjugation_preserves_anomaly_freedom q u d l e hA, ?_⟩
  constructor
  · simpa using (full_CPT_preserves_matter q false t).trans hQ
  constructor
  · simpa using (full_CPT_preserves_matter u false t).trans hu
  constructor
  · simpa using (full_CPT_preserves_matter d false t).trans hd
  constructor
  · simpa using (full_CPT_preserves_matter l false t).trans hl
  · simpa using (full_CPT_preserves_matter e false t).trans he

end GppSMGenerationRelationalOrientationLock
