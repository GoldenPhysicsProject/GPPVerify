import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The arithmetic TFD Gram kernel: GCD covariance and Möbius whitening

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-28_tfd_gcd_mobius_whitening.md` (commit `1105b9d`).

On `ℓ²(ℕ) ⊗ ℓ²(ℕ)` let `V_d = S_d ⊗ S_d` with `S_d e_n = e_{dn}`, and take the thermal vector
`Ω_β = ζ(β)^{-1/2} Σ n^{-β/2} e_n ⊗ e_n` (`β > 1`). The note's exact claims include the
following.

* **§1. GCD Gram kernel.** `⟨V_m Ω_β, V_n Ω_β⟩ = (ab)^{-β/2} = (gcd(m,n)/√(mn))^β`, where
  `m = ga` and `n = gb`. The combinatorial heart is that the solutions of `m k = n j` are exactly
  `(k, j) = (b t, a t)`. `mul_eq_mul_iff` proves this, so the double sum defining the inner
  product collapses to `(ab)^{-β/2} ζ(β)`. `gcd_kernel_eq` proves
  `(ab)^{-β/2} = (g/√(mn))^β`.
* **§3. Local whitening.** With `ω_k = r^k`, `(I − rS) ω = e₀` (`whitening_local`). So the local
  Möbius factor `I − rS` sends the local TFD vector to the vacuum.
* **§6. Positive Gram determinants carry the von Mangoldt current.**
  `det [[1, r], [r, 1]] = 1 − r²` (`gram_det`). For `p > 1`,
  `d/dβ log(1 − p^{-β}) = log p / (p^β − 1)` (`hasDerivAt_log_one_sub`), and
  `Σ_{k≥1} (log p) p^{-kβ} = log p / (p^β − 1)` (`hasSum_prime_power_current`).

All three were checked by hand as well; no corrections. §3's operator order is right:
`(I − rS)(I − rS*)` has corner entry `1`, while the reverse order would give `(1 + r²) I`.

## Scope

Not formalized: the Hilbert-space construction of `Ω_β` and `V_d`, the infinite sum in §1, the
inverse-covariance identity on `ℓ²(ℕ₀)`, the global Möbius product and its strong limit (§4),
the `β → 1` Hagedorn limit (§5), and the completed free-energy ratio (§7). The note makes no RH
claim.
-/

namespace GppTFDGCDMobius

/-- **The solutions of `m k = n j`.** With `g = gcd(m,n)`, `m = g a` and `n = g b`: `m k = n j` iff
`k = b t` and `j = a t` for some `t`. -/
theorem mul_eq_mul_iff (m n k j : ℕ) (hm : 0 < m) (hn : 0 < n) :
    m * k = n * j ↔ ∃ t, k = n / Nat.gcd m n * t ∧ j = m / Nat.gcd m n * t := by
  set g := Nat.gcd m n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left n hm
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left m n
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right m n
  rw [← hg] at ha hb
  have hma : m / g = a := by rw [ha, Nat.mul_div_cancel_left _ hg0]
  have hnb : n / g = b := by rw [hb, Nat.mul_div_cancel_left _ hg0]
  have hcop : Nat.Coprime a b := by
    have := Nat.coprime_div_gcd_div_gcd (m := m) (n := n) hg0
    rwa [← hg, hma, hnb] at this
  rw [hma, hnb]
  constructor
  · intro h
    have h' : a * k = b * j := by
      apply Nat.eq_of_mul_eq_mul_left hg0
      calc g * (a * k) = m * k := by rw [ha]; ring
        _ = n * j := h
        _ = g * (b * j) := by rw [hb]; ring
    have hbk : b ∣ k := by
      have : b ∣ a * k := ⟨j, h'⟩
      exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
    obtain ⟨t, rfl⟩ := hbk
    refine ⟨t, rfl, ?_⟩
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hb; omega)
    apply Nat.eq_of_mul_eq_mul_left hb0
    rw [← h']; ring
  · rintro ⟨t, rfl, rfl⟩
    rw [ha, hb]; ring

/-- **The GCD kernel value.** With `m = g a` and `n = g b` (`g > 0`), and any real `β`,
`(ab)^{-β/2} = (g/√(mn))^β`. -/
theorem gcd_kernel_eq (g a b β : ℝ) (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) :
    (a * b) ^ (-β / 2) = (g / Real.sqrt ((g * a) * (g * b))) ^ β := by
  have hab : 0 < a * b := mul_pos ha hb
  have hs : Real.sqrt ((g * a) * (g * b)) = g * Real.sqrt (a * b) := by
    rw [show (g * a) * (g * b) = g ^ 2 * (a * b) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hg.le]
  rw [hs, div_mul_cancel_left₀ hg.ne', Real.sqrt_eq_rpow, Real.inv_rpow (by positivity),
    ← Real.rpow_mul hab.le, ← Real.rpow_neg hab.le]
  congr 1; ring

/-- **Local whitening.** With `ω_k = r^k`, `(I − rS) ω = e₀`, where `S` is the unilateral shift
`(S ω)_{k+1} = ω_k` and `(S ω)_0 = 0`. -/
theorem whitening_local (r : ℝ) (k : ℕ) :
    r ^ k - (if k = 0 then 0 else r * r ^ (k - 1)) = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp
  · simp [pow_succ]; ring

/-- The local `2 × 2` TFD Gram determinant: `det [[1, r], [r, 1]] = 1 − r²`. -/
theorem gram_det (r : ℝ) : !![1, r; r, 1].det = 1 - r ^ 2 := by
  rw [Matrix.det_fin_two_of]; ring

/-- **The von Mangoldt current as a log-derivative of a positive determinant.** For `p > 1`,
`d/dβ log(1 − p^{-β}) = log p / (p^β − 1)`. -/
theorem hasDerivAt_log_one_sub (p β : ℝ) (hp : 1 < p) (hβ : 0 < β) :
    HasDerivAt (fun x => Real.log (1 - p ^ (-x))) (Real.log p / (p ^ β - 1)) β := by
  have hp0 : 0 < p := by linarith
  have hlt : p ^ (-β) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hpos : 0 < 1 - p ^ (-β) := by linarith
  have hd : HasDerivAt (fun x => p ^ (-x)) (p ^ (-β) * Real.log p * (-1)) β := by
    have := (hasDerivAt_neg β).const_rpow hp0
    convert this using 1; ring
  have h := (hd.const_sub 1).log hpos.ne'
  convert h using 1
  have hone : 1 < p ^ β := Real.one_lt_rpow hp hβ
  rw [Real.rpow_neg hp0.le]
  field_simp [hone.ne', (sub_pos.mpr hone).ne']

/-- **The prime-power current.** For `p > 1` and `β > 0`,
`Σ_{k≥0} (log p) p^{-(k+1)β} = log p / (p^β − 1)`. -/
theorem hasSum_prime_power_current (p β : ℝ) (hp : 1 < p) (hβ : 0 < β) :
    HasSum (fun k : ℕ => Real.log p * (p ^ (-β)) ^ (k + 1)) (Real.log p / (p ^ β - 1)) := by
  have hp0 : 0 < p := by linarith
  set q := p ^ (-β) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hgeo := hasSum_geometric_of_lt_one hq0 hq1
  have h := hgeo.mul_left (Real.log p * q)
  have hone : 1 < p ^ β := Real.one_lt_rpow hp hβ
  have hqinv : q = (p ^ β)⁻¹ := by rw [hq, Real.rpow_neg hp0.le]
  have e1 : (fun k : ℕ => Real.log p * q ^ (k + 1)) = fun k => Real.log p * q * q ^ k := by
    funext k; ring
  have e2 : Real.log p / (p ^ β - 1) = Real.log p * q * (1 - q)⁻¹ := by
    rw [hqinv]; field_simp [hone.ne', (sub_pos.mpr hone).ne']
  rw [e1, e2]; exact h

end GppTFDGCDMobius
