import GppVerify.RiemannHypothesis.EtaInversionLog
import GppVerify.RiemannHypothesis.MoebiusTsum

/-!
# Möbius inversion of the logarithmic Euler sum

With `ℓ(t) = log (1 - e^{-t})` and `K(t) = Σ_{m ≥ 1} ℓ(m t)`, Möbius inversion over multiples gives

  `Σ_{n ≥ 1} μ(n) K(n t) = ℓ(t)`   for `t > 0`.

The weighted summability `Σ N |ℓ(N t)| < ∞` follows from `|ℓ(x)| ≤ e^{-x}/(1 - e^{-x})` and the
geometric weight `N e^{-N t}`.  This recovers the single-mode logarithm `ℓ(t)` from the whole
Euler sum, the inversion that turns the symmetric structure of `K` (`K_symm`) into a statement
about one mode.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GppEtaInversion

/-- The single-mode logarithm `ℓ(t) = log (1 - e^{-t})`. -/
noncomputable def ell (t : ℝ) : ℝ := Real.log (1 - Real.exp (-t))

theorem abs_ell_le {x : ℝ} (hx : 0 < x) : |ell x| ≤ Real.exp (-x) / (1 - Real.exp (-x)) := by
  have hq : Real.exp (-x) < 1 := exp_neg_lt_one hx
  have hpos : 0 < 1 - Real.exp (-x) := by linarith
  have hle : ell x ≤ 0 := Real.log_nonpos hpos.le (by linarith [Real.exp_pos (-x)])
  have hge : 1 - (1 - Real.exp (-x))⁻¹ ≤ ell x := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_of_nonpos hle]
  have : (1 - Real.exp (-x))⁻¹ - 1 = Real.exp (-x) / (1 - Real.exp (-x)) := by
    field_simp
    ring
  linarith

theorem summable_weighted_ell {t : ℝ} (ht : 0 < t) :
    Summable fun N : ℕ+ => (N : ℝ) * |ell (N * t)| := by
  have hq : Real.exp (-t) < 1 := exp_neg_lt_one ht
  have hden : 0 < 1 - Real.exp (-t) := by linarith
  have hg : Summable fun N : ℕ => (N : ℝ) * Real.exp (-t) ^ N := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := Real.exp (-t))
      (by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hq)
  have hg' : Summable fun N : ℕ+ => (N : ℝ) * Real.exp (-t) ^ (N : ℕ) :=
    hg.comp_injective PNat.coe_injective
  refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
    (hg'.mul_right (1 - Real.exp (-t))⁻¹)
  have hNt : 0 < (N : ℝ) * t := by positivity
  have h1 := abs_ell_le hNt
  have h2 : Real.exp (-((N : ℝ) * t)) = Real.exp (-t) ^ (N : ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : 1 - Real.exp (-t) ≤ 1 - Real.exp (-t) ^ (N : ℕ) := by
    have : Real.exp (-t) ^ (N : ℕ) ≤ Real.exp (-t) :=
      pow_le_of_le_one (Real.exp_pos _).le hq.le N.pos.ne'
    linarith
  have h4 : |ell (N * t)| ≤ Real.exp (-t) ^ (N : ℕ) * (1 - Real.exp (-t))⁻¹ := by
    refine h1.trans ?_
    rw [h2, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hden h3) (by positivity)
  calc (N : ℝ) * |ell (N * t)| ≤ (N : ℝ) * (Real.exp (-t) ^ (N : ℕ) * (1 - Real.exp (-t))⁻¹) := by
        gcongr
    _ = (N : ℝ) * Real.exp (-t) ^ (N : ℕ) * (1 - Real.exp (-t))⁻¹ := by ring

/-- **Möbius inversion of the Euler sum.** `Σ_n μ(n) K(n t) = log (1 - e^{-t})` for `t > 0`. -/
theorem moebius_K {t : ℝ} (ht : 0 < t) :
    ∑' n : ℕ+, ((μ (n : ℕ) : ℤ) : ℝ) * K ((n : ℝ) * t) = ell t := by
  have hK : ∀ n : ℕ+, K ((n : ℝ) * t) = ∑' m : ℕ+, ell (((n * m : ℕ+) : ℝ) * t) := by
    intro n
    unfold K
    have h := tsum_pnat_eq_tsum_succ
      (f := fun m : ℕ => Real.log (1 - Real.exp (-((m : ℝ) * ((n : ℝ) * t)))))
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    refine tsum_congr (fun m => ?_)
    unfold ell
    congr 3
    push_cast
    ring
  calc ∑' n : ℕ+, ((μ (n : ℕ) : ℤ) : ℝ) * K ((n : ℝ) * t)
      = ∑' n : ℕ+, ((μ (n : ℕ) : ℤ) : ℝ) * ∑' m : ℕ+, ell (((n * m : ℕ+) : ℝ) * t) :=
        tsum_congr (fun n => by rw [hK n])
    _ = ell (((1 : ℕ+) : ℝ) * t) :=
        GppMoebiusTsum.moebius_tsum (fun N : ℕ+ => ell ((N : ℝ) * t)) (summable_weighted_ell ht)
    _ = ell t := by simp

end GppEtaInversion

#print axioms GppEtaInversion.abs_ell_le
#print axioms GppEtaInversion.summable_weighted_ell
#print axioms GppEtaInversion.moebius_K
