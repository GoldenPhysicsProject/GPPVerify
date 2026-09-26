import Mathlib.Tactic

/-!
# CPT-oriented index pair: global index cancels, relational index adds

A chiral Dirac index is odd under orientation reversal: reversing the orientation exchanges
positive and negative chirality, so the index changes sign.  The full analytic/geometric
index theorem is not reproved here.  This file isolates the exact integer bookkeeping once
a two-sheet pair has indices `k` and `-k`.

With sheet orientations `tau_+=+1` and `tau_-=-1`, the ordinary total index vanishes,

    k + (-k) = 0,

while the orientation-weighted index is

    (+1)k + (-1)(-k) = 2k.

This is the topological analogue of the project's relational charge `c*t`.  It motivates a
concrete cosmological target: if fermion-number production is controlled by a chiral index
or spectral flow, a globally CPT-symmetric doubled geometry may carry zero conventional
index while both sheets possess the same relational matter orientation.

The physical identification with electroweak baryon/lepton production requires the anomaly
and APS/spectral-flow bridge and is not asserted by these integer identities alone.
-/

namespace GppCPTOrientedIndexPair

/-- Conventional sum of opposite-orientation sheet indices. -/
def totalIndex (k : ℤ) : ℤ := k + (-k)

/-- Orientation-weighted sum for sheet signs +1 and -1. -/
def orientedIndex (k : ℤ) : ℤ := (1:ℤ)*k + (-1:ℤ)*(-k)

/-- Opposite sheet indices cancel globally. -/
theorem conventional_index_cancels (k : ℤ) : totalIndex k = 0 := by
  simp [totalIndex]

/-- The same pair adds in the relational/orientation-weighted index. -/
theorem oriented_index_adds (k : ℤ) : orientedIndex k = 2*k := by
  simp [orientedIndex]
  ring

/-- A nonzero sheet index can coexist with exactly zero global conventional index. -/
theorem nonzero_sheet_index_with_zero_global
    (k : ℤ) (hk : k ≠ 0) :
    totalIndex k = 0 ∧ orientedIndex k ≠ 0 := by
  constructor
  · exact conventional_index_cancels k
  · rw [oriented_index_adds]
    exact mul_ne_zero (by norm_num) hk

end GppCPTOrientedIndexPair
