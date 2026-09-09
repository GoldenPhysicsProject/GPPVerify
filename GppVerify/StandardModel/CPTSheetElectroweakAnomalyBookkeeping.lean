import Mathlib.Tactic

/-!
# Two-sheet electroweak anomaly bookkeeping

For an electroweak topological transition of integer winding/index `k`, the Standard-Model
chiral anomaly gives, for `Ngen` generations, the familiar bookkeeping

    Delta B = Ngen * k,
    Delta L = Ngen * k,

so `Delta(B-L)=0` and `Delta(B+L)=2*Ngen*k`.

Under orientation/CPT reversal the topological index changes sign, so the mirror sheet has
`-k` and hence opposite conventional `Delta B` and `Delta L`.  The global conventional
changes cancel between the two sheets, while weighting by the opposite sheet orientations
makes the relational changes add.

The anomaly coefficient itself is standard QFT input and is encoded here by the definitions;
this module proves the exact two-sheet consequences.  It does not prove that the Big Bang
realizes a nonzero electroweak index or fixes its magnitude.
-/

namespace GppCPTSheetElectroweakAnomalyBookkeeping

/-- Baryon-number change associated with `Ngen` generations and topological index `k`. -/
def deltaB (Ngen k : ℤ) : ℤ := Ngen*k

/-- Lepton-number change in the same transition. -/
def deltaL (Ngen k : ℤ) : ℤ := Ngen*k

def deltaBminusL (Ngen k : ℤ) : ℤ := deltaB Ngen k - deltaL Ngen k
def deltaBplusL (Ngen k : ℤ) : ℤ := deltaB Ngen k + deltaL Ngen k

/-- Electroweak topology preserves B-L in this bookkeeping. -/
theorem BminusL_preserved (Ngen k : ℤ) : deltaBminusL Ngen k = 0 := by
  simp [deltaBminusL, deltaB, deltaL]

/-- It changes B+L by twice the generation-weighted topological index. -/
theorem BplusL_change (Ngen k : ℤ) :
    deltaBplusL Ngen k = 2*Ngen*k := by
  simp [deltaBplusL, deltaB, deltaL]
  ring

/-- Opposite-orientation sheets carry opposite conventional baryon changes. -/
theorem mirror_baryon_change_opposite (Ngen k : ℤ) :
    deltaB Ngen (-k) = -deltaB Ngen k := by
  simp [deltaB]
  ring

/-- Hence the two-sheet conventional baryon change cancels globally. -/
theorem two_sheet_baryon_change_cancels (Ngen k : ℤ) :
    deltaB Ngen k + deltaB Ngen (-k) = 0 := by
  rw [mirror_baryon_change_opposite]
  ring

/-- But after multiplying each sheet by its own orientation sign, the relational baryon
    changes have the same sign and add. -/
theorem two_sheet_oriented_baryon_change_adds (Ngen k : ℤ) :
    (1:ℤ)*deltaB Ngen k + (-1:ℤ)*deltaB Ngen (-k) =
      2*deltaB Ngen k := by
  rw [mirror_baryon_change_opposite]
  ring

/-- The same package holds for lepton number. -/
theorem two_sheet_lepton_package (Ngen k : ℤ) :
    deltaL Ngen k + deltaL Ngen (-k) = 0 ∧
    (1:ℤ)*deltaL Ngen k + (-1:ℤ)*deltaL Ngen (-k) =
      2*deltaL Ngen k := by
  constructor <;> simp [deltaL] <;> ring

end GppCPTSheetElectroweakAnomalyBookkeeping
