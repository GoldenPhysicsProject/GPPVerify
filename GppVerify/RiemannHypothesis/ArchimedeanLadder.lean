import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The real-place boundary density as a pole mode minus the trivial-zero ladder

Source: Codex, GPPDiscovery2 `research/2026-09-27_archimedean_pole_trivial_zero_ladder.md`, the
opening exact decomposition.

For `x > 0` let `w_∞(x) = e^{-x/2} + e^{x/2} − e^{-x/2}/(1 − e^{-2x})`.

* `w_infty_ladder`: `w_∞(x) = e^{x/2} − Σ_{k ≥ 1} e^{-(2k + 1/2) x}` (the `k = 0` term of the thermal
  series cancels the explicit `e^{-x/2}`);
* `ladder_pole`: the `k`-th mode `e^{-(2k+1/2)x}` has Laplace pole `r = −(2k + 1/2)`, i.e.
  `s = 1/2 + r = −2k` — the trivial zeros `s = −2, −4, …` for `k ≥ 1`, and `s = 0` for the cancelled
  `k = 0` mode; the growing mode `e^{x/2}` has pole `r = 1/2`, i.e. `s = 1`.

## Checks and scope

Both claims check. As the note's own clarification says, "pole mode" refers to the isolated real-place
summand: the full completed `ξ` has no pole at `s = 1`. **Not formalized:** the renormalized Laplace
formula with `ψ(r/2 + 1/4)`, the convergence of the subtracted boundary distribution, the identification
with Gibbs escape, and any physical reading. No RH claim.
-/

open Real

namespace GppArchimedeanLadder

/-- The completed real-place boundary density. -/
noncomputable def wInfty (x : ℝ) : ℝ :=
  Real.exp (-x / 2) + Real.exp (x / 2) - Real.exp (-x / 2) / (1 - Real.exp (-2 * x))

/-- **Pole mode minus trivial-zero ladder.** -/
theorem w_infty_ladder (x : ℝ) (hx : 0 < x) :
    HasSum (fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * x))
      (Real.exp (x / 2) - wInfty x) := by
  have hq0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-x / 2) * Real.exp (-2 * x))
  have e : (fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * x)) =
      fun k : ℕ => Real.exp (-x / 2) * Real.exp (-2 * x) * Real.exp (-2 * x) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have h1 : 1 - Real.exp (-2 * x) ≠ 0 := by linarith
  have hv : Real.exp (x / 2) - wInfty x =
      Real.exp (-x / 2) * Real.exp (-2 * x) * (1 - Real.exp (-2 * x))⁻¹ := by
    unfold wInfty
    generalize Real.exp (-x / 2) = a at *
    generalize Real.exp (-2 * x) = q at *
    generalize Real.exp (x / 2) = E
    field_simp
    ring
  rw [e, hv]
  exact hg

/-- **Ladder poles sit at the trivial zeros.** `r + (2k + 1/2) = 0` with `s = 1/2 + r` iff `s = −2k`. -/
theorem ladder_pole (k : ℕ) (s : ℝ) : (s - 1 / 2) + (2 * (k : ℝ) + 1 / 2) = 0 ↔ s = -2 * (k : ℝ) := by
  constructor <;> intro h <;> linarith

/-- The growing mode `e^{x/2}` has its pole at `s = 1`. -/
theorem growing_pole (s : ℝ) : (s - 1 / 2) - 1 / 2 = 0 ↔ s = 1 := by
  constructor <;> intro h <;> linarith

end GppArchimedeanLadder
