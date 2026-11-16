import GppVerify.RiemannHypothesis.WeilHRhoCore

/-!
# (H-ρ) Gershgorin check: rows 651..739

`decide +kernel` evaluates `rowOk` (see `WeilHRhoCore.lean`) for these rows. Sharded so each file's
kernel run stays short.
-/

namespace GppWeilHRho

theorem rows_7 : (List.range' 651 89).all rowOk = true := by decide +kernel

end GppWeilHRho

#print axioms GppWeilHRho.rows_7
