import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The prime Cayley / Dirac two-channel identities, and the summable repeated returns

Source: Codex, GPP-bridge `research/codex/` (commit `a0ab790`):
* `2026-10-02_prime_energy_cayley_two_channel_weyl.md`, §§1–2, and the numerical audit
  `experiments/prime_cayley_two_channel_weyl_check.py` in GPPDiscovery2 (`fd23a30`);
* `2026-10-02_primitive_channel_reduction.md`, the `m ≥ 3` estimate.

**Local Cayley data at a prime.** Put `A = p^{-1/2}` and `L = log p`. The note's exact local
identities, checked here at the scalar level:

* `cayley_eq_tanh`: `c_p = (√p − 1)/(√p + 1) = tanh(log p / 4)`.
* `coupling_eq_one_iff`: `μ_p = 2/√(p − 1)` equals `1` iff `p = 5`.
* `channel_entries`: with `μ = μ_p`, `μ/√(μ² + 4) = p^{-1/2}` and `2/√(μ² + 4) = √(1 − 1/p)`.
  So the two-channel matrix `S(μ_p)` is `[[q, b], [b, −q]]` with `q = p^{-1/2}` and
  `b = √(1 − 1/p)`, the matrix Codex's script audits.

**The two-channel matrix is a reflection.** `D(μ) = μ σ_z + 2 σ_x = [[μ, 2], [2, −μ]]` has
`D² = (μ² + 4) I` (`dirac_sq`). So `S(μ) = D/√(μ² + 4)` is symmetric with `S² = I`
(`channel_symm`, `channel_sq`). At `p = 5`, `S = (1/√5) [[1, 2], [2, −1]]`
(`channel_five`).

**Repeated prime returns are summable** (`repeated_returns_summable`):
`Σ_p (log p) p^{-3/2} / (1 − p^{-1/2}) < ∞`. This sum is `Σ_p Σ_{m≥3} (log p) p^{-m/2}`
(`repeated_returns_hasSum`), so the `m ≥ 3` part of the prime-power sum is `O(1)`. That is the
note's `R_{≥3}(L) = O(1)`.

Checked by hand with the note. One sharpening, recorded in `CLAUDE_CODE_RESEARCH_NOTES.md` and
not formalized here: `R_2(L) = O(L)` by Mertens' theorem, not merely `O(L²)`.

## Scope

Local `2 × 2` algebra and one convergent prime sum. The note's coupled prime-side
Herglotz/Schur construction, and the reduction of RH to the primitive channel
`Σ_{p ≤ x} log p/√p = 2√x + O((log x)^M)`, are not formalized. No RH claim.
-/

open Matrix

namespace GppPrimeCayley

/-- `c_p = (√p − 1)/(√p + 1) = tanh(log p / 4)` for `p > 0`. -/
theorem cayley_eq_tanh (p : ℝ) (hp : 0 < p) :
    (Real.sqrt p - 1) / (Real.sqrt p + 1) = Real.tanh (Real.log p / 4) := by
  set t := Real.exp (Real.log p / 4) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht2 : t ^ 2 = Real.sqrt p := by
    rw [ht, ← Real.exp_nat_mul, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
    congr 1; push_cast; ring
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, ← ht, ← ht2]
  have : t ^ 2 + 1 ≠ 0 := by positivity
  field_simp

/-- `μ_p = 2/√(p − 1)` equals `1` iff `p = 5` (for `p > 1`). -/
theorem coupling_eq_one_iff (p : ℝ) (hp : 1 < p) : 2 / Real.sqrt (p - 1) = 1 ↔ p = 5 := by
  have hs : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.mpr (by linarith)
  rw [div_eq_one_iff_eq hs.ne']
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ p - 1)] at h2
    linarith
  · rintro rfl
    rw [show (5 : ℝ) - 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The channel entries at a prime.** With `μ = 2/√(p − 1)` (`p > 1`):
`μ/√(μ² + 4) = p^{-1/2}` and `2/√(μ² + 4) = √(1 − 1/p)`. -/
theorem channel_entries (p : ℝ) (hp : 1 < p) :
    let μ := 2 / Real.sqrt (p - 1)
    μ / Real.sqrt (μ ^ 2 + 4) = 1 / Real.sqrt p ∧
      2 / Real.sqrt (μ ^ 2 + 4) = Real.sqrt (1 - 1 / p) := by
  intro μ
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hs1 : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.mpr hp1
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hroot : Real.sqrt (μ ^ 2 + 4) = 2 * Real.sqrt p / Real.sqrt (p - 1) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    simp only [μ]
    field_simp
    rw [Real.sq_sqrt hp1.le, Real.sq_sqrt hp0.le]
    ring
  refine ⟨?_, ?_⟩
  · rw [hroot]; simp only [μ]; field_simp
  · rw [hroot, show 1 - 1 / p = (p - 1) / p by field_simp, Real.sqrt_div' _ hp0.le]
    field_simp

/-- The Dirac matrix `D(μ) = μ σ_z + 2 σ_x`. -/
def dirac (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![μ, 2; 2, -μ]

/-- `D(μ)² = (μ² + 4) I`. -/
theorem dirac_sq (μ : ℝ) : dirac μ * dirac μ = (μ ^ 2 + 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dirac, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The two-channel matrix `S(μ) = D(μ)/√(μ² + 4)`. -/
noncomputable def channel (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt (μ ^ 2 + 4)) • dirac μ

/-- `S(μ)` is symmetric. -/
theorem channel_symm (μ : ℝ) : (channel μ)ᵀ = channel μ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [channel, dirac]

/-- **`S(μ)` is a reflection:** `S(μ)² = I`. -/
theorem channel_sq (μ : ℝ) : channel μ * channel μ = 1 := by
  have hpos : 0 < μ ^ 2 + 4 := by positivity
  have hs : Real.sqrt (μ ^ 2 + 4) * Real.sqrt (μ ^ 2 + 4) = μ ^ 2 + 4 :=
    Real.mul_self_sqrt hpos.le
  rw [channel, smul_mul_smul_comm, dirac_sq, smul_smul]
  convert one_smul ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ) using 2
  rw [div_mul_div_comm, one_mul, hs, one_div, inv_mul_cancel₀ hpos.ne']

/-- At `p = 5` (`μ = 1`): `S = (1/√5) [[1, 2], [2, −1]]`. -/
theorem channel_five : channel 1 = (1 / Real.sqrt 5) • !![1, 2; 2, -1] := by
  rw [channel, dirac]; norm_num

/-- **The `m ≥ 3` prime-power tail at one prime.** For `p > 1`,
`Σ_{m≥3} (log p) p^{-m/2} = (log p) p^{-3/2}/(1 − p^{-1/2})`. -/
theorem repeated_returns_hasSum (p : ℝ) (hp : 1 < p) :
    HasSum (fun k : ℕ => Real.log p * (p ^ (-(1 / 2 : ℝ))) ^ (k + 3))
      (Real.log p * p ^ (-(3 / 2 : ℝ)) / (1 - p ^ (-(1 / 2 : ℝ)))) := by
  have hp0 : 0 < p := by linarith
  set q := p ^ (-(1 / 2 : ℝ)) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have h3 : p ^ (-(3 / 2 : ℝ)) = q ^ 3 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.log p * q ^ 3)
  have e1 : (fun k : ℕ => Real.log p * q ^ (k + 3)) = fun k => Real.log p * q ^ 3 * q ^ k := by
    funext k; ring
  rw [h3, e1, div_eq_mul_inv]
  exact h

/-- **Repeated prime returns are summable:** `Σ_p (log p) p^{-3/2}/(1 − p^{-1/2}) < ∞`.
Hence `R_{≥3}(L) = O(1)`. -/
theorem repeated_returns_summable :
    Summable (fun p : Nat.Primes =>
      Real.log p * (p : ℝ) ^ (-(3 / 2 : ℝ)) / (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  have hmaj : Summable (fun p : Nat.Primes => 16 * (p : ℝ) ^ (-(5 / 4 : ℝ))) :=
    ((Nat.Primes.summable_rpow).mpr (by norm_num)).mul_left 16
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
  · have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have hq1 : (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
    have := Real.log_nonneg hp.le
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ p) (-(3 / 2 : ℝ))
    apply div_nonneg (by positivity) (by linarith)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    -- `p^{-1/2} ≤ 3/4`, so `1/(1 − p^{-1/2}) ≤ 4`.
    have hq : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
      rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, inv_le_comm₀ (Real.sqrt_pos.mpr hp0)
        (by norm_num), Real.le_sqrt (by norm_num) hp0.le]
      linarith
    have hden : 1 / 4 ≤ 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
    -- `log p ≤ 4 p^{1/4}`.
    have hlog : Real.log p ≤ 4 * (p : ℝ) ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 4)
      linarith [show (p : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (p : ℝ) ^ (1 / 4 : ℝ) by ring]
    have hr : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) = (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hp0]; norm_num
    have h32 : 0 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
    have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith)]
    calc Real.log p * (p : ℝ) ^ (-(3 / 2 : ℝ))
        ≤ 4 * (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlog h32
      _ = 4 * (p : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [mul_assoc, hr]
      _ = 16 * (p : ℝ) ^ (-(5 / 4 : ℝ)) * (1 / 4) := by ring
      _ ≤ 16 * (p : ℝ) ^ (-(5 / 4 : ℝ)) * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hden (by positivity)

end GppPrimeCayley
