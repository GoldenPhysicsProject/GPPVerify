import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The dual Möbius obstruction in the finite zeta-graph metric

Source: Codex, GPPDiscovery2 `research/2026-09-28_finite_zeta_graph_dual_mobius_obstruction.md`,
§§1–2.

On `S_N = {1, …, N}` the half-density zeta matrix is `Z_N(n,d) = √(d/n) 1_{d ∣ n}` with inverse
`M_N(n,d) = μ(n/d) √(d/n) 1_{d ∣ n}`. For the raw scalar character `a_z(n) = n^{-z}` the dual
representative is `b_{N,z} = M_N^T a_z`.

* `dual_coord_eq` (§1): `b_{N,z}(d) = d^{-z} Σ_{m ≤ N/d} μ(m) m^{-1/2-z}`, an exact identity
  with no zeros or analytic continuation;
* `dual_norm_ge` (§2): the `d = 1` coordinate gives the unconditional lower bound
  `Σ_d |b_{N,z}(d)|² ≥ |Σ_{m ≤ N} μ(m) m^{-1/2-z}|²`, i.e. the dual norm of the raw character is
  bounded below by `√H_N` times the weighted Möbius partial sum (`H_N` is the harmonic number
  normalization of the metric).

## Checks and scope

Both claims check. **Not formalized:** the equivalence in §3 between `A(N) = Σ_{m≤N} μ(m)/√m =
O(N^ε)` and the Mertens bound `M(x) = O(x^{1/2+ε})` (partial summation; it is the classical
RH-equivalent statement and is exactly why the raw critical character's dual norm is "another form
of the target"), and the block-diagonal discussion of §4. No RH claim.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GppDualMobius

/-- The `d`-th coordinate of `M_N^T a_z`: `Σ_{n ≤ N, d ∣ n} μ(n/d) √(d/n) n^{-z}`. -/
noncomputable def dualCoord (N : ℕ) (z : ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ (Icc 1 N).filter (d ∣ ·),
    ((μ (n / d) : ℤ) : ℂ) * ((Real.sqrt ((d : ℝ) / n) : ℝ) : ℂ) * (n : ℂ) ^ (-z)

/-- **Exact reciprocal-zeta form of the dual coordinate.** -/
theorem dual_coord_eq (N : ℕ) (z : ℂ) (d : ℕ) (hd : 0 < d) :
    dualCoord N z d =
      (d : ℂ) ^ (-z) * ∑ m ∈ Icc 1 (N / d), ((μ m : ℤ) : ℂ) * (m : ℂ) ^ (-(1 / 2 : ℂ) - z) := by
  have himg : (Icc 1 N).filter (d ∣ ·) = (Icc 1 (N / d)).image (d * ·) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · omega
        · exact hm
      · exact (Nat.le_div_iff_mul_le hd).mpr (by linarith [mul_comm d m])
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
      · exact Nat.mul_pos hd h1
      · calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d h2
          _ ≤ N := Nat.mul_div_le N d
  rw [dualCoord, himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hdq : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmq : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  rw [Nat.mul_div_cancel_left m hd]
  have e1 : ((d * m : ℕ) : ℂ) ^ (-z) = (d : ℂ) ^ (-z) * (m : ℂ) ^ (-z) := by
    push_cast
    exact Complex.natCast_mul_natCast_cpow d m (-z)
  have e2 : ((Real.sqrt ((d : ℝ) / ((d * m : ℕ) : ℝ)) : ℝ) : ℂ) = (m : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have h1 : (d : ℝ) / ((d * m : ℕ) : ℝ) = (m : ℝ)⁻¹ := by
      push_cast; field_simp
    have h2 : (m : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt m : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      have := Complex.ofReal_cpow (Nat.cast_nonneg m) (1 / 2 : ℝ)
      push_cast at this
      rw [← this]
    rw [h1, Real.sqrt_inv, Complex.cpow_neg, h2, Complex.ofReal_inv]
  rw [e1, e2, sub_eq_add_neg, Complex.cpow_add _ _ hmc]
  ring

/-- The squared dual norm (up to the harmonic normalization). -/
noncomputable def dualNormSq (N : ℕ) (z : ℂ) : ℝ := ∑ d ∈ Icc 1 N, ‖dualCoord N z d‖ ^ 2

/-- **Lower bound from the `d = 1` coordinate.** -/
theorem dual_norm_ge (N : ℕ) (hN : 1 ≤ N) (z : ℂ) :
    ‖∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℂ) * (m : ℂ) ^ (-(1 / 2 : ℂ) - z)‖ ^ 2 ≤ dualNormSq N z := by
  have h1 := dual_coord_eq N z 1 one_pos
  simp only [Nat.cast_one, Complex.one_cpow, one_mul, Nat.div_one] at h1
  have : ‖dualCoord N z 1‖ ^ 2 ≤ dualNormSq N z :=
    Finset.single_le_sum (f := fun d => ‖dualCoord N z d‖ ^ 2) (fun d _ => sq_nonneg _)
      (mem_Icc.mpr ⟨le_refl 1, hN⟩)
  rwa [h1] at this

end GppDualMobius
