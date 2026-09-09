import Mathlib.Tactic
import GppVerify.StandardModel.CPTSheetElectroweakAnomalyBookkeeping

/-!
# Electroweak-index obstruction: topology alone does not generate B-L

The electroweak chiral anomaly changes baryon and lepton number equally,

    Delta B = Ngen k,
    Delta L = Ngen k,

so `Delta(B-L)=0`.  Therefore a proposed primordial matter mechanism based ONLY on the
ordinary electroweak topological index cannot produce a nonzero B-L asymmetry from an
initial B-L-neutral state.

This is a genuine obstruction for the orientation programme, not a reason to hide the gap.
If a nonzero B-L seed is required for survival through the standard hot electroweak era, it
must come from an additional boundary/source sector (for example a lepton-number-violating
neutral-fermion sector), from a nonstandard thermal history, or from a mechanism which
protects a B+L source from washout.

The dynamical washout statement is external thermal QFT; this file proves the exact charge
bookkeeping obstruction.
-/

namespace GppElectroweakIndexBLObstruction

open GppCPTSheetElectroweakAnomalyBookkeeping

/-- Electroweak topological spectral flow alone has zero B-L source. -/
theorem electroweak_index_has_zero_BL_source (Ngen k : ℤ) :
    deltaB Ngen k - deltaL Ngen k = 0 := by
  simp [deltaB, deltaL]

/-- Therefore adding only this anomaly contribution cannot change an initial B-L value. -/
theorem electroweak_index_preserves_initial_BL
    (BL0 Ngen k : ℤ) :
    BL0 + (deltaB Ngen k - deltaL Ngen k) = BL0 := by
  rw [electroweak_index_has_zero_BL_source]
  simp

/-- In particular it cannot generate nonzero B-L from a neutral initial condition. -/
theorem no_BL_from_zero_by_EW_index_alone (Ngen k : ℤ) :
    (0 : ℤ) + (deltaB Ngen k - deltaL Ngen k) = 0 := by
  simp [deltaB, deltaL]

/-- If an independent lepton-number-violating boundary source `ell` is added with no direct
    baryon source, the resulting B-L seed is exactly `-ell`; the electroweak index still
    cancels out of B-L. -/
theorem neutral_lepton_source_controls_BL
    (Ngen k ell : ℤ) :
    (deltaB Ngen k) - (deltaL Ngen k + ell) = -ell := by
  simp [deltaB, deltaL]
  ring

/-- Thus electroweak topology can redistribute B+L while an independent lepton source fixes
    the conserved B-L datum. -/
theorem separation_of_EW_index_and_BL_source
    (Ngen k ell : ℤ) :
    (deltaB Ngen k - (deltaL Ngen k + ell) = -ell) ∧
    (deltaB Ngen k + deltaL Ngen k = 2*Ngen*k) := by
  exact ⟨neutral_lepton_source_controls_BL Ngen k ell,
    BplusL_change Ngen k⟩

end GppElectroweakIndexBLObstruction
