import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# CHSH Bell violation at the optimal angle configuration, and CKW monogamy

Source: `ONON5213.tex`, "Bell Inequalities from Haar Measure" (Theorem
`thm:bell-violation`, Steps 1–3) and "Monogamy of Entanglement" (Theorem
`thm:monogamy`, Step 3). Both results, as isolated pieces of trigonometry
and real-number algebra, are genuine and standard (this is textbook CHSH /
CKW material, not GPP-specific); the surrounding claim in the source that
"Haar measure on `Gr(2,4)` forces exactly the Tsirelson bound" is a much
stronger structural assertion that is *not* formalized here — only the
concrete numerical computation the source itself carries out.

## What is proved

* `chshValue_eq`: at the angle configuration `θ_ab=0, θ_ab'=π/2,
  θ_a'b=θ_a'b'=π/4` (source's Step 3), the CHSH combination
  `S = E(a,b) - E(a,b') + E(a',b) + E(a',b')` with `E(θ) = -cos θ`
  evaluates exactly to `-1 - √2`.
* `chshValue_exceeds_classical_bound`: `|S| = 1 + √2 > 2`, i.e. this
  configuration genuinely violates the classical (local hidden variable)
  CHSH bound `|S| ≤ 2` — the source's boxed numerical claim, reproduced
  as an exact inequality rather than a decimal approximation.
* `chshValue_within_tsirelson_bound`: `|S| ≤ 2√2`, i.e. this violation
  respects Tsirelson's bound (does not itself establish that `2√2` is the
  supremum over all quantum strategies — only that this particular
  configuration's value does not exceed it).
* `ckw_forces_zero_concurrence`: the source's Step 3 monogamy argument,
  as pure real algebra: if `1 + x² ≤ y² ≤ 1` (the CKW inequality
  `C_{A:B}² + C_{A:C}² ≤ C_{A:BC}²` specialized to maximal `C_{A:B} = 1`,
  together with the concurrence bound `C_{A:BC} ≤ 1`), then `x = 0`.
  Takes the CKW inequality itself as a hypothesis — it is not re-derived
  here, only the elementary consequence the source draws from it.

## What is not claimed

Nothing about *why* Haar measure on `Gr(2,4)` would force the Tsirelson
bound, nor the general CHSH operator formalism (Pauli observables, tensor
products, the quantum correlation function `E(a,b) = ⟨ψ|A_a⊗B_b|ψ⟩` for a
general state), is formalized. Only the source's own explicit numerical
evaluation at its chosen angles, and the elementary algebraic consequence
of the CKW inequality it states, are claimed.
-/

namespace GppCHSHViolation

open Real

/-- The quantum correlation function at the source's convention,
`E(θ) = -cos θ`, for the maximally entangled singlet state. -/
noncomputable def corr (θ : ℝ) : ℝ := -Real.cos θ

/-- The CHSH combination `S = E(a,b) - E(a,b') + E(a',b) + E(a',b')` at the
source's optimal angle configuration
`θ_ab = 0, θ_ab' = π/2, θ_a'b = θ_a'b' = π/4`. -/
noncomputable def chshValue : ℝ :=
  corr 0 - corr (Real.pi / 2) + corr (Real.pi / 4) + corr (Real.pi / 4)

/-- **The source's Step 3 computation**: `S = -1 - √2` exactly. -/
theorem chshValue_eq : chshValue = -1 - Real.sqrt 2 := by
  unfold chshValue corr
  rw [Real.cos_zero, Real.cos_pi_div_two, Real.cos_pi_div_four]
  ring

/-- **CHSH violation** (`thm:bell-violation`, boxed claim): `|S| = 1 + √2`,
strictly greater than the classical local-hidden-variable bound `2`. -/
theorem chshValue_exceeds_classical_bound : 2 < |chshValue| := by
  rw [chshValue_eq]
  have hsqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_gt_one : (1:ℝ) < Real.sqrt 2 := by
    have h2 : (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    rw [h2]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [abs_of_neg (by linarith)]
  linarith

/-- **Respects Tsirelson's bound**: `|S| ≤ 2√2` at this configuration
(does not establish `2√2` as the supremum over all configurations, only
that this one does not exceed it). -/
theorem chshValue_within_tsirelson_bound : |chshValue| ≤ 2 * Real.sqrt 2 := by
  rw [chshValue_eq, abs_of_neg (by
    have hsqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith)]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, hsq2]

/-- **CKW monogamy consequence** (`thm:monogamy`, Step 3): given the CKW
inequality `1 + x² ≤ y²` (maximal `A:B` entanglement forcing `C_{A:B}=1`)
together with `y² ≤ 1` (the concurrence bound `C_{A:BC} ≤ 1`), the
third-party concurrence `x` must vanish. -/
theorem ckw_forces_zero_concurrence {x y : ℝ} (h1 : 1 + x ^ 2 ≤ y ^ 2) (h2 : y ^ 2 ≤ 1) :
    x = 0 := by
  have hx2 : x ^ 2 ≤ 0 := by linarith
  have hx2' : x ^ 2 = 0 := le_antisymm hx2 (sq_nonneg x)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx2'

end GppCHSHViolation
