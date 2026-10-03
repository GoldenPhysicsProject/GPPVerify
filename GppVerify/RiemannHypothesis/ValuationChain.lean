import GppVerify.RiemannHypothesis.SelfDualDivisorGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Prime-power valuation chains: the local Gram matrix and the Euler factor as a Green function

Source: Codex, GPPDiscovery2 `research/2026-09-28_prime_valuation_chain_product_formula_sewing.md`,
§§1, 4.

* `valuation_gram`: on `ℤ/p^Kℤ` the subgroup states `v_a = |H_a|^{-1/2} 1_{H_a}`,
  `H_a = p^a ℤ/p^Kℤ`, have Gram matrix `⟨v_a, v_b⟩ = r^{|a−b|}` with `r = p^{-1/2}`: the prime-power
  tower is a one-dimensional Markov/Gaussian covariance chain in the valuation coordinate;
* `euler_green`: the one-sided Green function of the chain is the Euler factor,
  `Σ_{k≥0} p^{-k/2} e^{-ikt log p} = 1/(1 − p^{-1/2 - it})`.

## Checks and scope

Both claims check. `valuation_gram` is the `d = p^a`, `e = p^b` case of `GppSelfDualDivisor.gram_eq`.
**Not formalized:** the tridiagonal inverse (precision) matrix of `r^{|a−b|}` and its first-order
factorization `(I − rS)(I − rS^*)/(1 − r²)` (§3), Fourier as valuation reflection `a ↦ K − a`
(this is `GppFiniteSubgroupFourier.fourier_subgroup_state` for `d = p^a`, `M = p^{K−a}`, up to the
cast `p^a · p^{K−a} = p^K`), the CRT tensor factorization, and the product-formula sewing to the
Archimedean place (§§5 onward). No RH claim.
-/

open GppSelfDualDivisor

namespace GppValuationChain

/-- **The valuation-chain Gram matrix is `r^{|a−b|}`**, `r = p^{-1/2}`. -/
theorem valuation_gram (p K a b : ℕ) (hp : p.Prime) (haK : a ≤ K) (hbK : b ≤ K) :
    gram (p ^ K) (p ^ a) (p ^ b) = (1 / Real.sqrt p) ^ (max a b - min a b) := by
  have hp0 : 0 < p := hp.pos
  have hN : 0 < p ^ K := pow_pos hp0 K
  rw [gram_eq (p ^ K) (p ^ a) (p ^ b) hN (pow_pos hp0 a) (pow_pos hp0 b)
    (pow_dvd_pow p haK) (pow_dvd_pow p hbK)]
  have hg : Nat.gcd (p ^ a) (p ^ b) = p ^ min a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]; exact Nat.gcd_eq_left (pow_dvd_pow p h)
    · rw [min_eq_right h]; exact Nat.gcd_eq_right (pow_dvd_pow p h)
  rw [hg]
  set s : ℝ := Real.sqrt p with hs
  have hsp : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
  have hsq : s ^ 2 = p := Real.sq_sqrt (by exact_mod_cast hp0.le)
  have hnum : ((p ^ min a b : ℕ) : ℝ) = s ^ (2 * min a b) := by
    push_cast; rw [pow_mul, hsq]
  have hden : Real.sqrt (((p ^ a : ℕ) : ℝ) * ((p ^ b : ℕ) : ℝ)) = s ^ (a + b) := by
    have h : ((p ^ a : ℕ) : ℝ) * ((p ^ b : ℕ) : ℝ) = (s ^ (a + b)) ^ 2 := by
      push_cast
      rw [← pow_add, ← hsq, ← pow_mul, ← pow_mul, mul_comm]
    rw [h]
    exact Real.sqrt_sq (pow_nonneg hsp.le _)
  rw [hnum, hden, one_div, inv_pow]
  have hne : s ^ (a + b) ≠ 0 := pow_ne_zero _ hsp.ne'
  have hne2 : s ^ (max a b - min a b) ≠ 0 := pow_ne_zero _ hsp.ne'
  field_simp
  rw [← pow_add]
  congr 1
  omega

/-- **The Euler factor as the Green function of the valuation chain.** -/
theorem euler_green (p t : ℝ) (hp : 1 < p) :
    HasSum (fun k : ℕ => ((p : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)) ^ k)
      (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t))⁻¹ := by
  have hp0 : 0 < p := by linarith
  apply hasSum_geometric_of_norm_lt_one
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
  have : (-(1 / 2 : ℂ) - Complex.I * t).re = -(1 / 2) := by simp
  rw [this]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)

end GppValuationChain
