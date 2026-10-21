import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Uniform moment-tail certificate (finite and rational parts)

Source: Astra, GPP-bridge `work/2026-10-20_astra_uniform_moment_tail_certificate.md`.
Formalized by Claude Code, with AI assistance, for Daniel Toupin / Golden Physics Project.

* `sq_norm_replacement`: `|‖x‖² − ‖y‖²| ≤ 2‖y‖‖x−y‖ + ‖x−y‖²` in any real inner-product space,
  the abstract form of Astra's bound `|v*(H−H_m)v| ≤ 2√ρ‖v‖√(v*Sv) + ρ‖v‖²` (take `x = F`,
  `y = F_m` in the weighted `L²` space);
* `two_mul_le_eps`: `2ab ≤ εa² + b²/ε`, the step giving the operator sandwich
  `−[εS + (1+1/ε)ρI] ≤ H − H_m ≤ εS + (1+1/ε)ρI`;
* `certificate_step`: `ρ < δ` and `(δ−ρ)² > 4ρT` imply `2√(ρT) + ρ < δ`;
* `rhobar_lt`, `trbar_le`, `moment_tail_certificate`: for Astra's rational envelopes
  `Ī_p = 1000^{1−p}(4106/(p−1) + 1/(p−1)²)`, `ρ̄ = 17·7⁴⁸·Ī₅₀/(1−7/1000)²` and
  `T̄ = 17 Σ_{r,q<24, r+q even} 7^{r+q} Ī_{r+q+2}`, we prove `ρ̄ < 10⁻¹⁰⁰`, `T̄ ≤ 17·576·4107/1000`
  (a crude bound; the exact value is about `69.8`), and hence `2√(ρ̄T̄) + ρ̄ < 10⁻⁴⁵`.

Scope: the analytic chain linking `ρ̄, T̄` to the actual tail integrals (endpoint-moment expansion,
the integral `I_p`, the digamma envelope `|w_L(t)| ≤ log|t| + b` with `b < 4096`) is Astra's written
argument and is not formalized here. The certificate controls one fixed 17-mode block's frequency
tail only; it is not a positivity certificate for the Weil form, its complement, or RH.
-/

open Finset

namespace GppMomentTail

/-- Core replacement bound: `|‖x‖² − ‖y‖²| ≤ 2‖y‖‖x−y‖ + ‖x−y‖²`. -/
theorem sq_norm_replacement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ 2 * ‖y‖ * ‖x - y‖ + ‖x - y‖ ^ 2 := by
  have h1 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have := norm_add_le y (x - y); simpa using this
  have h2 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have := norm_add_le x (y - x); rw [norm_sub_rev] at this; simpa using this
  have hx := norm_nonneg x; have hy := norm_nonneg y; have hd := norm_nonneg (x - y)
  rw [abs_le]; constructor <;> nlinarith

/-- Weighted AM–GM used for the operator sandwich: `2ab ≤ ε a² + b²/ε`. -/
theorem two_mul_le_eps {a b ε : ℝ} (hε : 0 < ε) : 2 * a * b ≤ ε * a ^ 2 + b ^ 2 / ε := by
  have h : 0 ≤ (ε * a - b) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  have : (ε * a - b) ^ 2 / ε = ε * a ^ 2 - 2 * a * b + b ^ 2 / ε := by
    field_simp; ring
  linarith

/-- The arithmetic step of Astra's certificate: from `ρ < δ` and `(δ−ρ)² > 4ρT` conclude
`2√(ρT) + ρ < δ`. -/
theorem certificate_step {ρ T δ : ℝ} (hρ : 0 ≤ ρ) (hT : 0 ≤ T) (h1 : ρ < δ)
    (h2 : 4 * ρ * T < (δ - ρ) ^ 2) : 2 * Real.sqrt (ρ * T) + ρ < δ := by
  have hpos : 0 < δ - ρ := by linarith
  have hsq : Real.sqrt (ρ * T) ^ 2 = ρ * T := Real.sq_sqrt (mul_nonneg hρ hT)
  have hs : 2 * Real.sqrt (ρ * T) < δ - ρ := by
    apply lt_of_pow_lt_pow_left₀ 2 hpos.le
    nlinarith
  linarith

/-- `Ī_p = 1000^{1−p} (4106/(p−1) + 1/(p−1)²)` for `p ≥ 2`, Astra's rational tail-integral envelope. -/
def Ibar (p : ℕ) : ℚ := (4106 / (p - 1 : ℚ) + 1 / (p - 1 : ℚ) ^ 2) / 1000 ^ (p - 1)

/-- `ρ̄ = 17 · 7^48 · Ī_50 / (1 − 7/1000)²`. -/
def rhobar : ℚ := 17 * 7 ^ 48 * Ibar 50 / (1 - 7 / 1000) ^ 2

/-- `T̄ = 17 Σ_{r,q<24, r+q even} 7^{r+q} Ī_{r+q+2}`. -/
def trbar : ℚ := 17 * ∑ r ∈ range 24, ∑ q ∈ range 24,
  if (r + q) % 2 = 0 then 7 ^ (r + q) * Ibar (r + q + 2) else 0

theorem rhobar_lt : rhobar < 1 / 10 ^ 100 := by
  unfold rhobar Ibar; norm_num

theorem Ibar_shift (k : ℕ) :
    Ibar (k + 2) = (4106 / ((k : ℚ) + 1) + 1 / ((k : ℚ) + 1) ^ 2) / 1000 ^ (k + 1) := by
  unfold Ibar
  rw [show k + 2 - 1 = k + 1 by omega]
  push_cast; ring_nf

theorem Ibar_nonneg (k : ℕ) : 0 ≤ Ibar (k + 2) := by
  rw [Ibar_shift]; positivity

theorem Ibar_term_le (k : ℕ) : 7 ^ k * Ibar (k + 2) ≤ 4107 / 1000 := by
  rw [Ibar_shift]
  set X := 4106 / ((k : ℚ) + 1) + 1 / ((k : ℚ) + 1) ^ 2 with hX
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hle : X ≤ 4107 := by
    have a : 4106 / ((k : ℚ) + 1) ≤ 4106 := div_le_self (by norm_num) (by linarith)
    have b : 1 / ((k : ℚ) + 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have h0 : 0 ≤ X := by positivity
  have h7 : (7 : ℚ) ^ k ≤ 1000 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hm : 7 ^ k * X ≤ 1000 ^ k * 4107 := mul_le_mul h7 hle h0 (by positivity)
  have hpos : (0 : ℚ) < 1000 ^ (k + 1) := by positivity
  rw [← mul_div_assoc, div_le_div_iff₀ hpos (by norm_num), pow_succ]
  nlinarith

theorem trbar_le : trbar ≤ 17 * 576 * (4107 / 1000) := by
  unfold trbar
  have : ∀ r ∈ range 24, ∑ q ∈ range 24,
      (if (r + q) % 2 = 0 then 7 ^ (r + q) * Ibar (r + q + 2) else 0) ≤ 24 * (4107 / 1000 : ℚ) := by
    intro r _
    calc _ ≤ ∑ q ∈ range 24, (4107 / 1000 : ℚ) := by
          apply sum_le_sum; intro q _
          split_ifs
          · exact Ibar_term_le _
          · norm_num
      _ = 24 * (4107 / 1000 : ℚ) := by simp
  have := sum_le_sum this
  simp only [sum_const, card_range, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

/-- Astra's exact certificate: `2√(ρ̄ T̄) + ρ̄ < 10⁻⁴⁵`. -/
theorem moment_tail_certificate :
    2 * Real.sqrt ((rhobar : ℝ) * trbar) + rhobar < 1 / 10 ^ 45 := by
  have hρ : (0 : ℚ) ≤ rhobar := by unfold rhobar Ibar; norm_num
  have hT : (0 : ℚ) ≤ trbar := by
    unfold trbar
    apply mul_nonneg (by norm_num)
    apply sum_nonneg; intro r _; apply sum_nonneg; intro q _
    split_ifs
    · exact mul_nonneg (by positivity) (Ibar_nonneg _)
    · exact le_refl 0
  have a : (rhobar : ℝ) < 1 / 10 ^ 100 := by
    have := (Rat.cast_lt (K := ℝ)).mpr rhobar_lt; push_cast at this; exact this
  have b : (trbar : ℝ) ≤ 17 * 576 * (4107 / 1000) := by
    have := (Rat.cast_le (K := ℝ)).mpr trbar_le; push_cast at this; exact this
  have a0 : (0:ℝ) ≤ rhobar := by exact_mod_cast hρ
  have b0 : (0:ℝ) ≤ trbar := by exact_mod_cast hT
  apply certificate_step a0 b0
  · linarith [show (1 : ℝ) / 10 ^ 100 < 1 / 10 ^ 45 by norm_num]
  · nlinarith

end GppMomentTail
