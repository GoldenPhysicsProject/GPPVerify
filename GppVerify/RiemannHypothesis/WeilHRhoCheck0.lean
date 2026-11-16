import GppVerify.RiemannHypothesis.WeilHRhoCore

/-!
# (H-ρ) Gershgorin check: rows 0..92

`decide +kernel` evaluates `rowOk` (see `WeilHRhoCore.lean`) for these rows. Sharded so each file's
kernel run stays short.
-/

namespace GppWeilHRho

theorem rows_0 : (List.range' 0 93).all rowOk = true := by decide +kernel

end GppWeilHRho

#print axioms GppWeilHRho.rows_0
