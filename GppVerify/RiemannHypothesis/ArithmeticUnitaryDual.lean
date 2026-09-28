import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.LSeries.RiemannZeta
import GppVerify.RiemannHypothesis.CasimirCriticalLine

/-!
# Why `½`: the prime-torus square-summability edge, and the Casimir trichotomy

Synthesis of 2026-09-28 (Claude Code, `CLAUDE_CODE_RESEARCH_NOTES.md`, "the global picture"),
cross-checked and sharpened by Codex (GPP-bridge PR #11 comment, 2026-09-28).

**1. The prime torus has its square-summability edge at `σ = ½`.** Lift zeta to the compact
torus `K = ∏_p S¹` dual to `ℚ₊^×`. Two objects live there, and Codex asked that they be kept
distinct.

* The full Bohr lift `Z_s = Σ_n n^{-s} χ_n` has `‖Z_s‖²_{H²(K)} = Σ_n n^{-2σ} = ζ(2σ)`. This is
  finite iff `σ > ½` (`full_lift_summable_iff`, and `full_lift_norm_sq`: the sum equals
  `ζ(2σ)`).
* The primitive prime-linear sector `Σ_p p^{-s} χ_p` has square norm `Σ_p p^{-2σ}`. This is
  also finite iff `σ > ½` (`prime_sector_summable_iff`).

Both edges sit at the critical line. So `½` is forced on the prime side by square
summability, independently of the Archimedean fact that `Re s = ½` is the unitary dual of
scaling on half-densities.

**2. The Casimir trichotomy.** Take `c = ρ(1−ρ)` and the `SL(2,ℝ)` convention in which the
principal series `Δ = ½ + iλ` has `c = ¼ + λ²`. Every `ρ` falls in one of the following cases
(`casimir_trichotomy`):

* `ρ` off the line and non-real: `c` is **not real**, so `ρ` is not a Casimir value of any
  unitary representation (`off_line_nonreal_casimir`);
* `Re ρ = ½`: `c` is real and `≥ ¼`, the principal-series range (`GppCasimirCriticalLine.casimir_ge_quarter_iff`);
* `ρ` real in `(0,1)`: `0 < c ≤ ¼`, with `c = ¼` only at `ρ = ½`. This is the
  complementary-series range (`real_strip_casimir`). ζ has no such zeros; that is classical and
  not formalized here.
* `ρ = −2n` with `n ≥ 1` (trivial zeros): `c = (1+2n)(−2n) < 0`, and it equals the Casimir
  value at `Δ = 1 + 2n` (`trivial_zero_casimir`). This matches discrete-series Casimir **values**
  only. No representation-theoretic identification is claimed.

## Scope and corrections

Nothing here locates a zero. The statement that would do so is that the nontrivial zeros are the
Casimir spectrum of a unitary representation constructed without zero data. That is equivalent
to RH and open.

Correction recorded with this file (Codex): the de Bruijn–Newman constant satisfies `Λ ≥ 0`
(Rodgers–Tao), and RH is equivalent to `Λ ≤ 0`. So RH *would imply* `Λ = 0`. It is **not**
known unconditionally that `Λ = 0`, so the "no slack" heuristic is conditional on RH.
-/

open GppCasimirCriticalLine

namespace GppArithmeticUnitaryDual

/-- **Full Bohr lift edge.** `Σ_n n^{-2σ}` converges iff `σ > ½`. -/
theorem full_lift_summable_iff (σ : ℝ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) ↔ 1 / 2 < σ := by
  rw [Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- **Prime-sector edge.** `Σ_p p^{-2σ}` converges iff `σ > ½`. -/
theorem prime_sector_summable_iff (σ : ℝ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 * σ)) ↔ 1 / 2 < σ := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **The full Bohr lift's square norm is `ζ(2σ)`.** For `σ > ½`,
`Σ_{n≥1} n^{-2σ} = ζ(2σ)`. -/
theorem full_lift_norm_sq (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ ((2 * σ : ℝ) : ℂ) = riemannZeta ((2 * σ : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith)]

/-- Off the line and off the real axis, the Casimir is not real. -/
theorem off_line_nonreal_casimir (ρ : ℂ) (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    (casimir ρ).im ≠ 0 := by
  intro h
  rcases (casimir_real_iff ρ).mp h with h1 | h1
  · exact hre h1
  · exact him h1

/-- **Complementary-series range.** For real `ρ ∈ (0,1)`: `0 < c ≤ ¼`, with `c = ¼` iff `ρ = ½`. -/
theorem real_strip_casimir (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    0 < (casimir x).re ∧ (casimir x).re ≤ 1 / 4 ∧ (casimir x).im = 0 ∧
      ((casimir x).re = 1 / 4 ↔ x = 1 / 2) := by
  have hre : (casimir x).re = x * (1 - x) := by simp [casimir_re]
  have him : (casimir x).im = 0 := by rw [casimir_im]; simp
  refine ⟨by rw [hre]; nlinarith, by rw [hre]; nlinarith [sq_nonneg (x - 1 / 2)], him, ?_⟩
  rw [hre]
  constructor
  · intro h; nlinarith [sq_nonneg (x - 1 / 2)]
  · intro h; rw [h]; norm_num

/-- **Trivial zeros match discrete-series Casimir values.** For `n ≥ 1`,
`c(−2n) = c(1 + 2n) = (1+2n)(−2n) < 0`. -/
theorem trivial_zero_casimir (n : ℕ) (hn : 1 ≤ n) :
    casimir (-2 * n) = casimir (1 + 2 * n) ∧ (casimir (-2 * (n : ℂ))).re < 0 := by
  refine ⟨by simp only [casimir]; ring, ?_⟩
  rw [casimir_re]
  simp
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- **The Casimir trichotomy.** Every `ρ` has a non-real Casimir, or lies on the critical line
(real Casimir `≥ ¼`), or is real (real Casimir `≤ ¼`). -/
theorem casimir_trichotomy (ρ : ℂ) :
    (casimir ρ).im ≠ 0 ∨
      (ρ.re = 1 / 2 ∧ (casimir ρ).im = 0 ∧ 1 / 4 ≤ (casimir ρ).re) ∨
      (ρ.im = 0 ∧ (casimir ρ).im = 0 ∧ (casimir ρ).re ≤ 1 / 4) := by
  by_cases h : (casimir ρ).im = 0
  · rcases (casimir_real_iff ρ).mp h with h1 | h1
    · exact Or.inr (Or.inl ⟨h1, (casimir_ge_quarter_iff ρ).mpr h1⟩)
    · refine Or.inr (Or.inr ⟨h1, h, ?_⟩)
      rw [casimir_re, h1]
      nlinarith [sq_nonneg (ρ.re - 1 / 2)]
  · exact Or.inl h

end GppArithmeticUnitaryDual
