import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The conductor-five quartic Gauss-sum operator: `B_χ*B_χ = 5/16(1 − P₅)`, `B_χB_χ̄ = −5/16(1 − P₅)`

Source: Codex, GPP-bridge `work/codex/2026-10-13_quartic_bc_haar_spinor_gauss_signed_pairing.md` §1.

Let `ζ = e^{2πi/5}` and let `χ` be the primitive quartic character mod 5 with `χ(1) = 1`,
`χ(2) = i`, `χ(3) = −i`, `χ(4) = −1` (and `χ(0) = 0`). On the Bost–Connes diagonal `C(Ẑ)`, the
operator `B_χ = ¼ Σ_{a=1}^{4} χ̄(a) e(a/5)` acts on `z ∈ Ẑ` through `x = z mod 5` as
`B_χ(x) = ¼ Σ_a χ̄(a) ζ^{ax}`. This file proves, for every natural `x`:
* `B_eq`: `B_χ(x) = χ(x) τ̄ / 4` with `τ̄ = Σ_a χ̄(a) ζ^a` (Gauss-sum reindexing; `B_χ(x) = 0` when
  `5 ∣ x`).
* `tau_mul_conj`: `τ̄ · conj τ̄ = 5`.
* `B_mul_conj`: `B_χ(x) · conj B_χ(x) = 5/16` if `5 ∤ x`, and `0` if `5 ∣ x`. This is the pointwise form of
  `B_χ* B_χ = (5/16)(1 − P₅)`.
* `conj_B`: `conj B_χ(x) = −B_χ̄(x)`, since `χ(−1) = −1`.
* `B_mul_Bbar`: `B_χ(x) · B_χ̄(x) = −5/16` if `5 ∤ x`, and `0` otherwise.

So the Hermitian square is positive and the unreflected opposite-character product is negative. The
sign is forced by the parity of `χ`. The Bost–Connes algebra itself, the KMS expectations, and the
`L(s,χ)` Mellin period are audited but **not formalized here**. **No RH claim.**
-/

namespace GppQuarticGaussFive

open Complex

/-- `ζ = e^{2πi/5}`. -/
noncomputable def ζ : ℂ := exp (2 * Real.pi * I / 5)

theorem zeta_prim : IsPrimitiveRoot ζ 5 := Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem zeta_pow_five : ζ ^ 5 = 1 := zeta_prim.pow_eq_one

theorem geom : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have := zeta_prim.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ, add_assoc] using this

theorem conj_zeta : (starRingEnd ℂ) ζ = ζ ^ 4 := by
  have hn : ‖ζ‖ = 1 := zeta_prim.norm'_eq_one (by norm_num)
  have hc : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have h4 : ζ ^ 4 * ζ = 1 := by rw [← pow_succ]; exact zeta_pow_five
  have hz : ζ ≠ 0 := zeta_prim.ne_zero (by norm_num)
  exact mul_right_cancel₀ hz (hc.trans h4.symm)

/-- The quartic character mod 5, as a function of the residue. -/
def chi : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => I
  | 3 => -I
  | 4 => -1
  | _ => 0

/-- `χ̄(a) = conj χ(a)`. -/
def chibar : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => -I
  | 3 => I
  | 4 => -1
  | _ => 0

/-- `τ̄ = Σ_a χ̄(a) ζ^a`. -/
noncomputable def taubar : ℂ := ζ - I * ζ ^ 2 + I * ζ ^ 3 - ζ ^ 4

/-- `τ = Σ_a χ(a) ζ^a`. -/
noncomputable def tau : ℂ := ζ + I * ζ ^ 2 - I * ζ ^ 3 - ζ ^ 4

/-- `B_χ(x) = ¼ Σ_{a=1}^{4} χ̄(a) ζ^{ax}`. -/
noncomputable def B (x : ℕ) : ℂ :=
  (1 / 4) * (ζ ^ x - I * ζ ^ (2 * x) + I * ζ ^ (3 * x) - ζ ^ (4 * x))

/-- `B_χ̄(x) = ¼ Σ_{a=1}^{4} χ(a) ζ^{ax}`. -/
noncomputable def Bbar (x : ℕ) : ℂ :=
  (1 / 4) * (ζ ^ x + I * ζ ^ (2 * x) - I * ζ ^ (3 * x) - ζ ^ (4 * x))

theorem zeta_pow_mod (n : ℕ) : ζ ^ n = ζ ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, zeta_pow_five, one_pow, one_mul]

theorem B_mod (x : ℕ) : B x = B (x % 5) := by
  unfold B
  rw [zeta_pow_mod x, zeta_pow_mod (2 * x), zeta_pow_mod (3 * x), zeta_pow_mod (4 * x),
    zeta_pow_mod (x % 5), zeta_pow_mod (2 * (x % 5)), zeta_pow_mod (3 * (x % 5)),
    zeta_pow_mod (4 * (x % 5))]
  simp [Nat.mul_mod]

theorem Bbar_mod (x : ℕ) : Bbar x = Bbar (x % 5) := by
  unfold Bbar
  rw [zeta_pow_mod x, zeta_pow_mod (2 * x), zeta_pow_mod (3 * x), zeta_pow_mod (4 * x),
    zeta_pow_mod (x % 5), zeta_pow_mod (2 * (x % 5)), zeta_pow_mod (3 * (x % 5)),
    zeta_pow_mod (4 * (x % 5))]
  simp [Nat.mul_mod]

/-- **Gauss-sum reindexing**: `B_χ(x) = χ(x mod 5) τ̄ / 4`. -/
theorem B_eq (x : ℕ) : B x = chi (x % 5) * taubar / 4 := by
  rw [B_mod]
  have h5 := zeta_pow_five
  have hr : x % 5 < 5 := Nat.mod_lt x (by norm_num)
  interval_cases (x % 5) <;> simp only [B, chi, taubar]
  · ring
  · ring
  · linear_combination (1 / 4 : ℂ) * (I * ζ - ζ ^ 3) * h5 + (1 / 4 : ℂ) * (ζ ^ 2 - ζ ^ 3) * Complex.I_sq
  · linear_combination (1 / 4 : ℂ) * (-I * ζ + I * ζ ^ 4 - ζ ^ 2 * (ζ ^ 5 + 1)) * h5
      - (1 / 4 : ℂ) * (ζ ^ 2 - ζ ^ 3) * Complex.I_sq
  · linear_combination (1 / 4 : ℂ) * (-I * ζ ^ 3 + I * ζ ^ 2 * (ζ ^ 5 + 1)
      - ζ * (ζ ^ 10 + ζ ^ 5 + 1)) * h5

/-- `B_χ̄(x) = χ̄(x mod 5) τ / 4`. -/
theorem Bbar_eq (x : ℕ) : Bbar x = chibar (x % 5) * tau / 4 := by
  rw [Bbar_mod]
  have h5 := zeta_pow_five
  have hr : x % 5 < 5 := Nat.mod_lt x (by norm_num)
  interval_cases (x % 5) <;> simp only [Bbar, chibar, tau]
  · ring
  · ring
  · linear_combination (1 / 4 : ℂ) * (-I * ζ - ζ ^ 3) * h5 + (1 / 4 : ℂ) * (ζ ^ 2 - ζ ^ 3) * Complex.I_sq
  · linear_combination (1 / 4 : ℂ) * (I * ζ - I * ζ ^ 4 - ζ ^ 2 * (ζ ^ 5 + 1)) * h5
      - (1 / 4 : ℂ) * (ζ ^ 2 - ζ ^ 3) * Complex.I_sq
  · linear_combination (1 / 4 : ℂ) * (I * ζ ^ 3 - I * ζ ^ 2 * (ζ ^ 5 + 1)
      - ζ * (ζ ^ 10 + ζ ^ 5 + 1)) * h5

/-- `conj τ̄ = −τ` (because `χ(−1) = −1`). -/
theorem conj_taubar : (starRingEnd ℂ) taubar = -tau := by
  have h5 := zeta_pow_five
  simp only [taubar, tau, map_sub, map_add, map_mul, map_pow, conj_zeta, Complex.conj_I]
  linear_combination (I * ζ ^ 3 - I * ζ ^ 2 * (ζ ^ 5 + 1) - ζ * (ζ ^ 10 + ζ ^ 5 + 1)) * h5

/-- `τ̄ τ = −5`. -/
theorem taubar_mul_tau : taubar * tau = -5 := by
  simp only [taubar, tau]
  linear_combination (ζ ^ 3 + ζ - 4) * zeta_pow_five + geom + (-(ζ ^ 2 - ζ ^ 3) ^ 2) * Complex.I_sq

/-- **`|τ̄|² = 5`**. -/
theorem tau_mul_conj : taubar * (starRingEnd ℂ) taubar = 5 := by
  rw [conj_taubar, mul_neg, taubar_mul_tau, neg_neg]

theorem chi_mul_conj (r : ℕ) (hr : r < 5) :
    chi r * (starRingEnd ℂ) (chi r) = if r = 0 then 0 else 1 := by
  interval_cases r <;> simp [chi, Complex.conj_I, ← sq, Complex.I_sq]

/-- **Hermitian square**: `B_χ(x) · conj B_χ(x) = 5/16` if `5 ∤ x`, else `0`. -/
theorem B_mul_conj (x : ℕ) :
    B x * (starRingEnd ℂ) (B x) = if x % 5 = 0 then 0 else 5 / 16 := by
  rw [B_eq]
  have h := chi_mul_conj (x % 5) (Nat.mod_lt x (by norm_num))
  simp only [map_div₀, map_mul, map_ofNat]
  calc chi (x % 5) * taubar / 4 * ((starRingEnd ℂ) (chi (x % 5)) * (starRingEnd ℂ) taubar / 4)
      = (chi (x % 5) * (starRingEnd ℂ) (chi (x % 5))) * (taubar * (starRingEnd ℂ) taubar) / 16 := by
        ring
    _ = _ := by rw [h, tau_mul_conj]; split_ifs <;> norm_num

/-- `conj B_χ(x) = −B_χ̄(x)`. -/
theorem conj_B (x : ℕ) : (starRingEnd ℂ) (B x) = -Bbar x := by
  rw [B_eq, Bbar_eq]
  have hr := Nat.mod_lt x (by norm_num : 0 < 5)
  simp only [map_div₀, map_mul, map_ofNat, conj_taubar]
  interval_cases (x % 5) <;> simp [chi, chibar, Complex.conj_I] <;> ring

/-- **Unreflected opposite-character product**: `B_χ(x) B_χ̄(x) = −5/16` if `5 ∤ x`, else `0`. -/
theorem B_mul_Bbar (x : ℕ) : B x * Bbar x = -(if x % 5 = 0 then 0 else 5 / 16) := by
  rw [← B_mul_conj, conj_B, mul_neg, neg_neg]

end GppQuarticGaussFive
