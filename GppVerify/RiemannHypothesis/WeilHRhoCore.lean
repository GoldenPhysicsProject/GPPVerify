import GppVerify.RiemannHypothesis.WeilHRhoData

/-!
# (H-ρ) Gershgorin check: the row predicate

`rowOk j` is the exact integer row-sum bound `dDev j + Σ_k sSym j k ≤ 3632727590` (`= ⌈0.8458103 · 2³²⌉`,
Flint's `gershgorin_bound_from_export`). `decide +kernel` evaluates it for all `j < 740` in eight shards
(`WeilHRhoCheck0 … 7`); `WeilHRho.lean` turns that into the real quadratic-form bound.
-/

namespace GppWeilHRho

/-- `2³² ρ`, with `ρ = 3632727590 / 2³² ≈ 0.84581`. -/
def rowBound : ℕ := 3632727590

def rowOk (j : ℕ) : Bool := decide (dDev j + ∑ k ∈ Finset.range 740, sSym j k ≤ rowBound)

end GppWeilHRho
