import GppVerify.RiemannHypothesis.WeilHRhoCore

/-!
# (H-ρ) Gershgorin check: rows 93..185

`decide +kernel` evaluates `rowOk` (see `WeilHRhoCore.lean`) for these rows. Sharded so each file's
kernel run stays short.
-/

namespace GppWeilHRho

theorem rows_1 : (List.range' 93 93).all rowOk = true := by decide +kernel

end GppWeilHRho

#print axioms GppWeilHRho.rows_1
