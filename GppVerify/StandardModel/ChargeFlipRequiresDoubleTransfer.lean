import Mathlib.Tactic

/-!
# Flipping a subsystem charge requires transfer of twice that charge

Let a subsystem carry signed charge q and an environment/reservoir carry charge r.
If the subsystem is changed from q to -q while total electric charge is conserved, the
reservoir must change by +2q:

    q + r = (-q) + (r + 2q).

Thus changing an electron-like charge -e into a positron-like charge +e changes the
subsystem by +2e and requires the rest of the closed system to absorb -2e.  Conversely a
+e to -e flip requires +2e to be deposited elsewhere.

This is elementary charge bookkeeping, but it cleanly distinguishes charge conjugation as a
formal map from a physically enacted process in a closed system.  Pair condensates are a
natural way for an environment to supply or absorb this two-charge difference.
-/

namespace GppChargeFlipRequiresDoubleTransfer

/-- Total charge of subsystem plus reservoir. -/
def totalCharge (q r : ℤ) : ℤ := q + r

/-- Reservoir charge required after flipping subsystem q -> -q. -/
def compensatedReservoir (q r : ℤ) : ℤ := r + 2*q

/-- Exact conservation law for a compensated charge flip. -/
theorem compensated_flip_conserves_total (q r : ℤ) :
    totalCharge (-q) (compensatedReservoir q r) = totalCharge q r := by
  simp [totalCharge, compensatedReservoir]
  ring

/-- The subsystem's charge change under q -> -q is exactly -2q. -/
theorem subsystem_flip_change (q : ℤ) :
    (-q) - q = -2*q := by ring

/-- The compensating reservoir change is exactly +2q. -/
theorem reservoir_compensation_change (q r : ℤ) :
    compensatedReservoir q r - r = 2*q := by
  simp [compensatedReservoir]
  ring

/-- Electron-sign example in units where e=1: -1 -> +1 requires reservoir change -2. -/
theorem electron_to_positron_requires_minus_two (r : ℤ) :
    totalCharge 1 (r-2) = totalCharge (-1) r := by
  simp [totalCharge]

/-- Positive-to-negative example: +1 -> -1 requires reservoir change +2. -/
theorem positive_to_negative_requires_plus_two (r : ℤ) :
    totalCharge (-1) (r+2) = totalCharge 1 r := by
  simp [totalCharge]

end GppChargeFlipRequiresDoubleTransfer
