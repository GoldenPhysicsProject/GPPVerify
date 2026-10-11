import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# A single prime's Gaussian heat amplitude is not reflection positive in heat time

Source: Codex, 2026-10-11, "transport OS+KMS into arithmetic physically" (GPP-bridge
`work/codex/2026-10-11_os_kms_critical_arithmetic_transport.md`, §3, and PR #11 comment
6106986739). The heat side of the completed explicit formula is
`K(t) = (4πt)^{-1/2} ⟨ν_∞ − ν_primes, e^{−x²/4t}⟩`. A natural hope is that the positive
prime measure transfers Osterwalder–Schrader (Hankel) positivity into `K` term by term.

It does not. For one prime length `a = log p` the mixed heat amplitude is
`g_a(t) = (4πt)^{-1/2} e^{−a²/(4t)}`. At the heat times `t₁ = 3a²/16` and `t₂ = 5a²/16`,
the 2×2 OS–Hankel matrix `[[g(2t₁), g(t₁+t₂)], [g(t₁+t₂), g(2t₂)]]` has **negative
determinant** for **every** `a ≠ 0`:

  `g(2t₁) g(2t₂) / g(t₁+t₂)² = 4 e^{−1/15} / √15 < 1`.

The ratio is independent of `a`, and `e^{2/15} ≥ 17/15 > 16/15` gives the inequality.

* `gaussian_ratio`: the exact ratio identity.
* `gaussian_hankel_det_neg`: the determinant is negative for every `a ≠ 0`.

Scope: this is a no-go for the **naive** positive transfer through Gaussian
subordination. `g_a` is a mixed amplitude `⟨δ_a, e^{tΔ} δ_0⟩`, not a diagonal norm, so
no OS positivity is to be expected. It says nothing about the completed `K(t)`, whose OS
positivity is RH-equivalent (v34 heat criterion). The Archimedean/Gamma part must actively
restore positivity. No RH claim.
-/

namespace GppNoGo.GaussianHeatOS

open Real

/-- The one-dimensional heat amplitude between points at distance `a`. -/
noncomputable def g (a t : ℝ) : ℝ := exp (-(a ^ 2) / (4 * t)) / sqrt (4 * π * t)

/-- The 2×2 OS–Hankel determinant at heat times `t₁, t₂`. -/
noncomputable def hankelDet (a t₁ t₂ : ℝ) : ℝ :=
  g a (2 * t₁) * g a (2 * t₂) - g a (t₁ + t₂) ^ 2

lemma g_left (a : ℝ) (ha : a ≠ 0) :
    g a (2 * (3 * a ^ 2 / 16)) = exp (-(2 / 3)) / sqrt (3 * π * a ^ 2 / 2) := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  unfold g
  congr 1
  · congr 1; field_simp; ring
  · congr 1; ring

lemma g_right (a : ℝ) (ha : a ≠ 0) :
    g a (2 * (5 * a ^ 2 / 16)) = exp (-(2 / 5)) / sqrt (5 * π * a ^ 2 / 2) := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  unfold g
  congr 1
  · congr 1; field_simp; ring
  · congr 1; ring

lemma g_mid (a : ℝ) (ha : a ≠ 0) :
    g a (3 * a ^ 2 / 16 + 5 * a ^ 2 / 16) = exp (-(1 / 2)) / sqrt (2 * π * a ^ 2) := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  unfold g
  congr 1
  · congr 1; field_simp; ring
  · congr 1; ring

/-- **Exact ratio.** `g(2t₁) g(2t₂) = (4 e^{−1/15}/√15) · g(t₁+t₂)²` for every `a ≠ 0`. -/
theorem gaussian_ratio (a : ℝ) (ha : a ≠ 0) :
    g a (2 * (3 * a ^ 2 / 16)) * g a (2 * (5 * a ^ 2 / 16)) =
      4 * exp (-(1 / 15)) / sqrt 15 * g a (3 * a ^ 2 / 16 + 5 * a ^ 2 / 16) ^ 2 := by
  rw [g_left a ha, g_right a ha, g_mid a ha]
  have hA : 0 < π * a ^ 2 := mul_pos pi_pos (by positivity)
  have h15 : (0 : ℝ) < sqrt 15 := sqrt_pos.mpr (by norm_num)
  have hs3 : sqrt (3 * π * a ^ 2 / 2) * sqrt (5 * π * a ^ 2 / 2) = π * a ^ 2 / 2 * sqrt 15 := by
    rw [← sqrt_mul (by positivity),
      show 3 * π * a ^ 2 / 2 * (5 * π * a ^ 2 / 2) = (π * a ^ 2 / 2) ^ 2 * 15 by ring,
      sqrt_mul (by positivity), sqrt_sq (by positivity)]
  have hs2 : sqrt (2 * π * a ^ 2) ^ 2 = 2 * π * a ^ 2 := sq_sqrt (by positivity)
  have he1 : exp (-(2 / 3)) * exp (-(2 / 5)) = exp (-(1 / 15)) * exp (-(1 / 2)) ^ 2 := by
    rw [← exp_add, sq, ← exp_add, ← exp_add]; norm_num
  have hpos3 : 0 < sqrt (3 * π * a ^ 2 / 2) := sqrt_pos.mpr (by positivity)
  have hpos5 : 0 < sqrt (5 * π * a ^ 2 / 2) := sqrt_pos.mpr (by positivity)
  have hpos2 : 0 < sqrt (2 * π * a ^ 2) := sqrt_pos.mpr (by positivity)
  rw [div_mul_div_comm, hs3, div_pow, hs2, he1]
  field_simp
  ring

lemma ratio_lt_one : 4 * exp (-(1 / 15)) / sqrt 15 < 1 := by
  have h15 : (0 : ℝ) < sqrt 15 := sqrt_pos.mpr (by norm_num)
  rw [div_lt_one h15]
  -- square both sides: 16 e^{−2/15} < 15 ⇔ e^{2/15} > 16/15, and e^{2/15} ≥ 1 + 2/15
  have hexp : (17 / 15 : ℝ) ≤ exp (2 / 15) := by
    have := add_one_le_exp (2 / 15 : ℝ); linarith
  have hsq : (4 * exp (-(1 / 15))) ^ 2 < sqrt 15 ^ 2 := by
    rw [sq_sqrt (by norm_num), mul_pow, ← exp_nat_mul,
      show ((2 : ℕ) : ℝ) * -(1 / 15) = -(2 / 15) by norm_num, exp_neg]
    have hp : 0 < exp (2 / 15 : ℝ) := exp_pos _
    rw [show (4 : ℝ) ^ 2 * (exp (2 / 15))⁻¹ = 16 / exp (2 / 15) by ring, div_lt_iff₀ hp]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 h15.le hsq

/-- **No-go.** For every prime length `a ≠ 0`, the Gaussian heat amplitude fails 2×2
OS–Hankel positivity at `t₁ = 3a²/16`, `t₂ = 5a²/16`. -/
theorem gaussian_hankel_det_neg (a : ℝ) (ha : a ≠ 0) :
    hankelDet a (3 * a ^ 2 / 16) (5 * a ^ 2 / 16) < 0 := by
  unfold hankelDet
  rw [gaussian_ratio a ha]
  have hg : 0 < g a (3 * a ^ 2 / 16 + 5 * a ^ 2 / 16) := by
    unfold g
    exact div_pos (exp_pos _) (sqrt_pos.mpr (by
      have : 0 < a ^ 2 := by positivity
      nlinarith [pi_pos]))
  have := ratio_lt_one
  have hg2 : 0 < g a (3 * a ^ 2 / 16 + 5 * a ^ 2 / 16) ^ 2 := by positivity
  nlinarith

end GppNoGo.GaussianHeatOS
