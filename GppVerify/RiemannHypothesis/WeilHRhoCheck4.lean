import GppVerify.RiemannHypothesis.WeilHRhoCore

/-!
# (H-ρ) Gershgorin check: rows 372..464

`decide +kernel` evaluates `rowOk` (see `WeilHRhoCore.lean`) for these rows. Sharded so each file's
kernel run stays short.
-/

namespace GppWeilHRho

theorem rows_4 : (List.range' 372 93).all rowOk = true := by decide +kernel

end GppWeilHRho

#print axioms GppWeilHRho.rows_4
