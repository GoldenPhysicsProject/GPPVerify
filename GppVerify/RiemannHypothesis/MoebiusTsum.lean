import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Möbius inversion for sums over multiples

For a sequence `a : ℕ+ → ℝ` with `Σ N |a N|`-weighted summability `Σ N * |a N| < ∞`,

  `Σ_{n ≥ 1} μ(n) · Σ_{m ≥ 1} a (n m) = a 1`.

The proof reindexes the double sum over `ℕ+ × ℕ+` along `(n, m) ↦ n m` using
`Nat.sigmaAntidiagonalEquivProd`, bounds the number of divisors by `N` (`Nat.card_divisors_le_self`)
for absolute summability, and evaluates the fiber sum `Σ_{d | N} μ(d) = [N = 1]`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace GppMoebiusTsum

/-- The fiber sum of the Möbius function over the divisor antidiagonal is `[N = 1]`. -/
theorem sum_antidiagonal_moebius (N : ℕ) :
    ∑ x ∈ Nat.divisorsAntidiagonal N, ((μ x.1 : ℤ) : ℝ) = if N = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f N) (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.mul_apply] at h
  have h2 : ∑ x ∈ Nat.divisorsAntidiagonal N, ((μ x.1 : ℤ) : ℝ) =
      ∑ x ∈ Nat.divisorsAntidiagonal N, ((μ : ArithmeticFunction ℝ) x.1) * ((ζ : ArithmeticFunction ℝ) x.2) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx2 : x.2 ≠ 0 := by
      intro hz
      have h := Nat.mem_divisorsAntidiagonal.1 hx
      rw [hz, mul_zero] at h
      exact h.2 h.1.symm
    simp [hx2]
  rw [h2, h]
  simp [ArithmeticFunction.one_apply]

/-- **Möbius inversion for sums over multiples.** If `Σ N |a N| < ∞` (weighted by `N`), then
`Σ_n μ(n) Σ_m a (n m) = a 1`. -/
theorem moebius_tsum (a : ℕ+ → ℝ) (ha : Summable fun N : ℕ+ => (N : ℝ) * |a N|) :
    ∑' n : ℕ+, ((μ (n : ℕ) : ℤ) : ℝ) * ∑' m : ℕ+, a (n * m) = a 1 := by
  let e := sigmaAntidiagonalEquivProd
  let G : (Σ N : ℕ+, Nat.divisorsAntidiagonal N) → ℝ :=
    fun s => ((μ s.2.1.1 : ℤ) : ℝ) * a s.1
  have hG : Summable G := by
    refine Summable.of_norm ?_
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun N => Summable.of_finite, ?_⟩
    refine Summable.of_nonneg_of_le (fun N => tsum_nonneg (fun _ => norm_nonneg _))
      (fun N => ?_) ha
    simp only [G, norm_mul, Real.norm_eq_abs, tsum_fintype, Finset.univ_eq_attach]
    rw [(N : ℕ).divisorsAntidiagonal.sum_attach (fun x : ℕ × ℕ => |((μ x.1 : ℤ) : ℝ)| * |a N|),
      Nat.sum_divisorsAntidiagonal (fun i _ => |((μ i : ℤ) : ℝ)| * |a N|)]
    calc ∑ i ∈ (N : ℕ).divisors, |((μ i : ℤ) : ℝ)| * |a N|
        ≤ ∑ i ∈ (N : ℕ).divisors, 1 * |a N| := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          gcongr
          exact_mod_cast abs_moebius_le_one (n := i)
      _ = ((N : ℕ).divisors.card : ℝ) * |a N| := by
          rw [Finset.sum_const, nsmul_eq_mul, one_mul]
      _ ≤ (N : ℝ) * |a N| := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self N
  have hf : ∀ p : ℕ+ × ℕ+, G (e.symm p) = ((μ (p.1 : ℕ) : ℤ) : ℝ) * a (p.1 * p.2) := fun p => rfl
  have hP : Summable fun p : ℕ+ × ℕ+ => ((μ (p.1 : ℕ) : ℤ) : ℝ) * a (p.1 * p.2) := by
    have := (e.symm.summable_iff (f := G)).2 hG
    simpa [Function.comp_def, hf] using this
  calc ∑' n : ℕ+, ((μ (n : ℕ) : ℤ) : ℝ) * ∑' m : ℕ+, a (n * m)
      = ∑' n : ℕ+, ∑' m : ℕ+, ((μ (n : ℕ) : ℤ) : ℝ) * a (n * m) := by
        refine tsum_congr (fun n => ?_)
        rw [tsum_mul_left]
    _ = ∑' p : ℕ+ × ℕ+, ((μ (p.1 : ℕ) : ℤ) : ℝ) * a (p.1 * p.2) := hP.tsum_prod.symm
    _ = ∑' s, G s := by
        rw [← e.symm.tsum_eq G]
        exact tsum_congr (fun p => (hf p).symm)
    _ = ∑' N : ℕ+, ∑' y : Nat.divisorsAntidiagonal (N : ℕ), G ⟨N, y⟩ := hG.tsum_sigma'
          (fun N => Summable.of_finite)
    _ = ∑' N : ℕ+, (if (N : ℕ) = 1 then (1 : ℝ) else 0) * a N := by
        refine tsum_congr (fun N => ?_)
        simp only [G, tsum_fintype, Finset.univ_eq_attach]
        rw [(N : ℕ).divisorsAntidiagonal.sum_attach (fun x : ℕ × ℕ => ((μ x.1 : ℤ) : ℝ) * a N),
          ← Finset.sum_mul, sum_antidiagonal_moebius]
    _ = a 1 := by
        rw [tsum_eq_single (1 : ℕ+)]
        · simp
        · intro N hN
          have : (N : ℕ) ≠ 1 := fun h => hN (PNat.coe_injective h)
          simp [this]

end GppMoebiusTsum

#print axioms GppMoebiusTsum.sum_antidiagonal_moebius
#print axioms GppMoebiusTsum.moebius_tsum
