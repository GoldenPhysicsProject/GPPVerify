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

/-!
## Scalar parameter geography (2026-11-07)

`Tempered` selects real Casimir at least `1/4`, not unitarity of every series.
`Complementary` selects the strict real interval `(0, 1/4)`; the midpoint
parameter `s = 1/2` belongs to `Tempered`, not to `Complementary`.
These are predicates on the existing `casimir`, not representation constructions.
The one-dimensional dictionary remains `Delta = s`. No zero is located here.

Source: Turbo's PR11 audits 6715094238, 6715112611, 6715124525 and
`MuseResearch/turbo-note-2026-11-07-{one-d-resolution,tempered-naming,tempered-geography}-audit.md`
in GoldenPhysicsProject/GPP-bridge. Core threshold, real/imaginary projections
and real-axis classification above retain their Codex / Claude Code provenance.
Daniel Toupin / Golden Physics Project; AI assistance from Principal series.
-/

/-- Scalar principal-series/tempered Casimir condition, not all unitary representations. -/
def Tempered (s : ℂ) : Prop := (casimir s).im = 0 ∧ 1 / 4 ≤ (casimir s).re

/-- Strict complementary Casimir range, excluding the threshold value `1/4`. -/
def Complementary (s : ℂ) : Prop :=
  (casimir s).im = 0 ∧ 0 < (casimir s).re ∧ (casimir s).re < 1 / 4

/-- The existing threshold equivalence, under the corrected scalar predicate name.
No strip or nonzero-height hypothesis is necessary. -/
theorem tempered_iff (s : ℂ) : Tempered s ↔ s.re = 1 / 2 :=
  casimir_ge_quarter_iff s

/-- Strict complementary parameters are precisely the real open segment off its midpoint. -/
theorem complementary_iff (s : ℂ) : Complementary s ↔
    s.im = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 := by
  constructor
  · rintro ⟨hc, hpos, hlt⟩
    have hne : s.re ≠ 1 / 2 := by
      intro h
      have ht := (casimir_ge_quarter_iff s).mpr h
      linarith [ht.2]
    have hi := ((casimir_real_iff s).mp hc).resolve_left hne
    rw [casimir_re, hi] at hpos
    refine ⟨hi, ?_, ?_, hne⟩
    · nlinarith [sq_nonneg s.re]
    · nlinarith [sq_nonneg (s.re - 1)]
  · rintro ⟨hi, h0, h1, hne⟩
    refine ⟨(casimir_real_iff s).mpr (Or.inr hi), ?_, ?_⟩
    · rw [casimir_re, hi]
      nlinarith [mul_pos h0 (sub_pos.mpr h1)]
    · rw [casimir_re, hi]
      have hsq := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
      nlinarith

/-- Non-real Casimir means off both the principal line and the real axis. -/
theorem complex_casimir_iff (s : ℂ) :
    (casimir s).im ≠ 0 ↔ s.re ≠ 1 / 2 ∧ s.im ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun hr => h ((casimir_real_iff s).mpr (Or.inl hr)),
      fun hi => h ((casimir_real_iff s).mpr (Or.inr hi))⟩
  · rintro ⟨hr, hi⟩
    exact off_line_nonreal_casimir s hr hi

/-- A scalar consequence of the existing real-Casimir classification. -/
theorem off_line_of_complex_casimir {s : ℂ} (h : (casimir s).im ≠ 0) :
    s.re ≠ 1 / 2 := ((complex_casimir_iff s).mp h).1

/-- In the open strip the three scalar cases cover every point.
This classifies parameters; it does not prove which case contains any zero. -/
theorem strip_geography (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    Tempered s ∨ Complementary s ∨ (casimir s).im ≠ 0 := by
  by_cases hr : s.re = 1 / 2
  · exact Or.inl ((tempered_iff s).mpr hr)
  · by_cases hi : s.im = 0
    · exact Or.inr (Or.inl ((complementary_iff s).mpr ⟨hi, h0, h1, hr⟩))
    · exact Or.inr (Or.inr (off_line_nonreal_casimir s hr hi))

/-- Actual complex Casimir at a shifted principal parameter.
The two signs of the shift are obtained by substituting `theta` and `-theta`. -/
theorem casimir_shifted_principal (θ γ : ℝ) :
    casimir ((1 / 2 : ℂ) + θ + γ * Complex.I) =
      1 / 4 + (γ : ℂ) ^ 2 - (θ : ℂ) ^ 2 - 2 * Complex.I * γ * θ := by
  unfold casimir
  linear_combination (-(γ : ℂ) ^ 2) * Complex.I_sq

/-- A nonzero shift at nonzero height has complex Casimir, not complementary Casimir.
The equivalence retains both degeneracies rather than assuming them away. -/
theorem casimir_shifted_nonreal_iff (θ γ : ℝ) :
    (casimir ((1 / 2 : ℂ) + θ + γ * Complex.I)).im ≠ 0 ↔ θ ≠ 0 ∧ γ ≠ 0 := by
  simp [complex_casimir_iff]

end GppArithmeticUnitaryDual
