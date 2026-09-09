import Mathlib.Tactic

/-!
# CPT-paired sheets: conventional charge cancels, relational charge adds

For a particle species choose a reference internal representation with signed charge scale
`e`.  Let `c = +/-1` denote representation orientation (`R` versus `R*`) and let
`t = +/-1` denote the microscopic/sheet temporal orientation relative to one external
bookkeeping convention.

The conventional charge label on a fixed sheet is

    Qconv = e*c,

while the proposed relational charge is

    Qrel = e*c*t.

A complete CPT/sheet reversal changes both microscopic orientations,

    (c,t) -> (-c,-t).

Hence conventional charge reverses but relational charge is invariant.  A CPT-paired
creation event can therefore create opposite conventional charges on opposite sheets with
zero total conventional charge while producing two copies of the same relational matter
orientation.

This is the exact finite algebra behind the proposed Big-Bang mechanism.  It does not yet
identify `Qrel` with baryon number, electric charge, or the full Standard-Model
representation-conjugacy label; those physical dictionaries must be established species by
species.
-/

namespace GppCPTSheetRelationalCharge

/-- Conventional fixed-sheet charge label. -/
def conventionalCharge (e c : ℝ) : ℝ := e*c

/-- Charge referred also to the microscopic/sheet temporal orientation. -/
def relationalCharge (e c t : ℝ) : ℝ := e*c*t

/-- Complete sheet/CPT reversal flips the conventional charge. -/
theorem mirror_flips_conventional_charge (e c : ℝ) :
    conventionalCharge e (-c) = - conventionalCharge e c := by
  simp [conventionalCharge]

/-- Complete reversal of BOTH microscopic orientations preserves relational charge. -/
theorem mirror_preserves_relational_charge (e c t : ℝ) :
    relationalCharge e (-c) (-t) = relationalCharge e c t := by
  simp [relationalCharge]
  ring

/-- A half flip of representation orientation reverses the relational charge. -/
theorem representation_half_flip_reverses_relational_charge (e c t : ℝ) :
    relationalCharge e (-c) t = - relationalCharge e c t := by
  simp [relationalCharge]
  ring

/-- A half flip of temporal orientation does the same. -/
theorem temporal_half_flip_reverses_relational_charge (e c t : ℝ) :
    relationalCharge e c (-t) = - relationalCharge e c t := by
  simp [relationalCharge]
  ring

/-- A CPT-paired two-sheet excitation has zero total conventional charge. -/
theorem CPT_pair_conventional_charge_cancels (e c : ℝ) :
    conventionalCharge e c + conventionalCharge e (-c) = 0 := by
  simp [conventionalCharge]
  ring

/-- But the same pair has two equal relational charges when the sheet orientation is also
    reversed. -/
theorem CPT_pair_relational_charge_adds (e c t : ℝ) :
    relationalCharge e c t + relationalCharge e (-c) (-t) =
      2 * relationalCharge e c t := by
  rw [mirror_preserves_relational_charge]
  ring

/-- In the canonical aligned pair `(c,t)=(+,+)` and `(-,-)`, both relational signs agree
    while the conventional charges cancel. -/
theorem canonical_CPT_pair_package (e : ℝ) :
    conventionalCharge e 1 + conventionalCharge e (-1) = 0 ∧
    relationalCharge e 1 1 = e ∧
    relationalCharge e (-1) (-1) = e ∧
    relationalCharge e 1 1 + relationalCharge e (-1) (-1) = 2*e := by
  constructor
  · norm_num [conventionalCharge]
  constructor
  · norm_num [relationalCharge]
  constructor <;> norm_num [relationalCharge]

end GppCPTSheetRelationalCharge
