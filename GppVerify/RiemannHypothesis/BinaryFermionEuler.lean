import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Binary fermionic encoding of a local Euler factor, and the Liouville correction

Source: Codex, GPP-bridge `work/codex/2026-10-13_prime_fermionic_fock_composite_theta_mirror_boundary.md`
(PR #11 comment 6155163571), with Claude Code's correction (comment 6155182173).

Writing each prime exponent in binary, `k = Σ_j 2^j ε_j` with `ε_j ∈ {0,1}`, turns the bosonic
local Euler factor into a product of fermionic two-level factors. With `x = p^{−s}`:
* `prod_binary`: `(1 − x) ∏_{j<N} (1 + x^{2^j}) = 1 − x^{2^N}` (binary telescoping), so
  `tendsto_prod_binary`: `∏_{j<N} (1 + x^{2^j}) → 1/(1 − x)` for `|x| < 1`. This is the local form of
  `ζ(s) = ∏_p ∏_j (1 + p^{−2^j s})`.
* `tendsto_prod_binary_succ`: `∏_{1≤j<N} (1 + x^{2^j}) → 1/(1 − x²)`.
* `liouville_local`: grading by the `j = 0` fermion parity on the **whole** Fock space gives the
  local factor `(1 − x)·1/(1 − x²) = 1/(1 + x)`, the Euler factor of `Σ λ(n) n^{−s} = ζ(2s)/ζ(s)`.
  It does **not** give `1 − x`, the Euler factor of `1/ζ(s)`. That one needs the projection onto
  the `j = 0` (squarefree) sector, where the local factor is just `1 − x`.

Exact local algebra only; the global Euler products are the standard ones. **No RH claim.**
-/

namespace GppBinaryFermionEuler

open Filter Topology Finset

/-- **Binary telescoping**: `(1 − x) ∏_{j<N} (1 + x^{2^j}) = 1 − x^{2^N}`. -/
theorem prod_binary (x : ℝ) (N : ℕ) :
    (1 - x) * ∏ j ∈ range N, (1 + x ^ 2 ^ j) = 1 - x ^ 2 ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ih, pow_succ, pow_mul]
    ring

theorem tendsto_pow_two_pow {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => x ^ 2 ^ N) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

/-- **Fermionic factorization of the local Euler factor**: `∏_{j<N} (1 + x^{2^j}) → 1/(1 − x)`. -/
theorem tendsto_prod_binary {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => ∏ j ∈ range N, (1 + x ^ 2 ^ j)) atTop (𝓝 (1 / (1 - x))) := by
  have h1 : (1 - x) ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this, abs_one] at hx; exact lt_irrefl _ hx
  have hlim : Tendsto (fun N : ℕ => (1 - x ^ 2 ^ N) / (1 - x)) atTop (𝓝 ((1 - 0) / (1 - x))) :=
    ((tendsto_const_nhds.sub (tendsto_pow_two_pow hx)).div_const _)
  rw [sub_zero] at hlim
  refine hlim.congr fun N => ?_
  rw [← prod_binary x N, mul_div_cancel_left₀ _ h1]

/-- Dropping the `j = 0` mode: `∏_{1≤j<N+1} (1 + x^{2^j}) → 1/(1 − x²)`. -/
theorem tendsto_prod_binary_succ {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => ∏ j ∈ range N, (1 + x ^ 2 ^ (j + 1))) atTop (𝓝 (1 / (1 - x ^ 2))) := by
  have hx2 : |x ^ 2| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg x) hx (by norm_num)
  refine (tendsto_prod_binary hx2).congr fun N => ?_
  refine prod_congr rfl fun j _ => ?_
  rw [← pow_mul, pow_succ, mul_comm]

/-- **Liouville correction (local)**: the whole-space `j = 0` parity grading gives
`(1 − x) · 1/(1 − x²) = 1/(1 + x)` (Euler factor of `ζ(2s)/ζ(s)`), not `1 − x`. -/
theorem liouville_local {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => (1 - x) * ∏ j ∈ range N, (1 + x ^ 2 ^ (j + 1))) atTop
      (𝓝 (1 / (1 + x))) := by
  have h1 : 1 + x ≠ 0 := by
    intro h; have : x = -1 := by linarith
    rw [this, abs_neg, abs_one] at hx; exact lt_irrefl _ hx
  have h2 : 1 - x ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this, abs_one] at hx; exact lt_irrefl _ hx
  have := (tendsto_prod_binary_succ hx).const_mul (1 - x)
  convert this using 2
  rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring]
  field_simp

/-- The Liouville local factor differs from the Möbius one `1 − x` unless `x = 0`. -/
theorem liouville_ne_moebius {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) : 1 / (1 + x) ≠ 1 - x := by
  have h1 : 1 + x ≠ 0 := by
    intro h; have : x = -1 := by linarith
    rw [this, abs_neg, abs_one] at hx; exact lt_irrefl _ hx
  intro h
  rw [div_eq_iff h1] at h
  have : x ^ 2 = 0 := by nlinarith
  exact hx0 (pow_eq_zero_iff (by norm_num) |>.mp this)

end GppBinaryFermionEuler
