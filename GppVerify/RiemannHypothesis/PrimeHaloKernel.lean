import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Prime.Basic

/-!
# The prime spectral halo kernel: finite core, monotone decay, vanishing at infinity

Source: Codex, GPPDiscovery2 `research/2026-09-26_prime_spectral_halo_kernel.md`, §1.

For `M ≥ 0`, `r ≥ 0`, the candidate real-place kernel built from the finite-place masses
`m_p = 2M/√(p−1)` and weights `w_p = 4/(p−1)²` is
`K(M, r) = 4 Σ_p exp(−2Mr/√(p−1)) / (p−1)²`. This file proves:
* `summable_weight`: `Σ_p 1/(p−1)²` converges, so `K` converges absolutely for every `r ≥ 0`.
* `kernel_zero`: `K(M, 0) = 4 Σ_p 1/(p−1)²`, a finite central core (numerically `≈ 5.500260`;
  this number is not certified here).
* `kernel_pos`: `K(M, r) > 0`.
* `kernel_antitone`: `K(M, ·)` is antitone on `[0, ∞)`.
* `kernel_tendsto_zero`: for `M > 0`, `K(M, r) → 0` as `r → ∞`.

**Not formalized:** the large-`r` asymptotic `K ~ 1/(M²r² log(2Mr))` (§2), which needs the
prime number theorem in integral form. The identification of `K` with a physical halo density is,
as the note says, a hypothesis. **No physics claim.**
-/

namespace GppPrimeHaloKernel

open Filter Topology

/-- The finite-place weight `1/(p−1)²` (the note's `w_p/4`). -/
noncomputable def weight (n : ℕ) : ℝ := 1 / ((n : ℝ) - 1) ^ 2

theorem summable_weight_nat : Summable weight := by
  rw [← summable_nat_add_iff 1]
  have := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  refine this.congr fun n => ?_
  simp [weight]

theorem summable_weight : Summable fun p : Nat.Primes => weight p :=
  summable_weight_nat.comp_injective Subtype.val_injective

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

/-- The prime spectral halo kernel. -/
noncomputable def kernel (M r : ℝ) : ℝ :=
  4 * ∑' p : Nat.Primes, Real.exp (-(2 * M * r / Real.sqrt ((p : ℝ) - 1))) * weight p

theorem term_le (M r : ℝ) (hMr : 0 ≤ M * r) (p : Nat.Primes) :
    Real.exp (-(2 * M * r / Real.sqrt ((p : ℝ) - 1))) * weight p ≤ weight p := by
  have hs := Real.sqrt_nonneg ((p : ℝ) - 1)
  have hexp : Real.exp (-(2 * M * r / Real.sqrt ((p : ℝ) - 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    apply div_nonneg _ hs; nlinarith
  nlinarith [weight_nonneg p, Real.exp_pos (-(2 * M * r / Real.sqrt ((p : ℝ) - 1)))]

theorem summable_terms (M r : ℝ) (hMr : 0 ≤ M * r) :
    Summable fun p : Nat.Primes => Real.exp (-(2 * M * r / Real.sqrt ((p : ℝ) - 1))) * weight p :=
  Summable.of_nonneg_of_le (fun p => mul_nonneg (Real.exp_pos _).le (weight_nonneg p))
    (term_le M r hMr) summable_weight

/-- **Finite central core**: `K(M, 0) = 4 Σ_p 1/(p−1)²`. -/
theorem kernel_zero (M : ℝ) : kernel M 0 = 4 * ∑' p : Nat.Primes, weight p := by
  simp [kernel]

theorem kernel_le_zero {M r : ℝ} (hMr : 0 ≤ M * r) : kernel M r ≤ kernel M 0 := by
  rw [kernel_zero, kernel]
  exact mul_le_mul_of_nonneg_left
    (Summable.tsum_le_tsum (term_le M r hMr) (summable_terms M r hMr) summable_weight)
    (by norm_num)

theorem two_prime : Nat.Prime 2 := Nat.prime_two

/-- **Positivity**: `K(M, r) > 0`. -/
theorem kernel_pos {M r : ℝ} (hMr : 0 ≤ M * r) : 0 < kernel M r := by
  unfold kernel
  apply mul_pos (by norm_num)
  refine (summable_terms M r hMr).tsum_pos (fun p => mul_nonneg (Real.exp_pos _).le
    (weight_nonneg p)) ⟨2, two_prime⟩ ?_
  apply mul_pos (Real.exp_pos _)
  simp [weight]

/-- **Monotone decay** in `r` for `M ≥ 0`. -/
theorem kernel_antitone {M : ℝ} (hM : 0 ≤ M) {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) :
    kernel M r₂ ≤ kernel M r₁ := by
  unfold kernel
  refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun p => ?_)
    (summable_terms M r₂ (mul_nonneg hM (h0.trans h12)))
    (summable_terms M r₁ (mul_nonneg hM h0))) (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (weight_nonneg p)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  nlinarith

theorem sqrt_pos_of_prime (p : Nat.Primes) : 0 < Real.sqrt ((p : ℝ) - 1) := by
  apply Real.sqrt_pos.mpr
  have : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  linarith

/-- **Vanishing at infinity**: for `M > 0`, `K(M, r) → 0` as `r → ∞`. -/
theorem kernel_tendsto_zero {M : ℝ} (hM : 0 < M) : Tendsto (kernel M) atTop (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => ∑' p : Nat.Primes,
      Real.exp (-(2 * M * r / Real.sqrt ((p : ℝ) - 1))) * weight p) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun p : Nat.Primes => weight p)
      (f := fun (r : ℝ) (p : Nat.Primes) =>
        Real.exp (-(2 * M * r / Real.sqrt ((p : ℝ) - 1))) * weight p)
      (g := fun _ => 0) summable_weight ?_ ?_
    · simpa using this
    · intro p
      have hs := sqrt_pos_of_prime p
      have h1 : Tendsto (fun r : ℝ => -(2 * M * r / Real.sqrt ((p : ℝ) - 1))) atTop atBot := by
        have : Tendsto (fun r : ℝ => (2 * M / Real.sqrt ((p : ℝ) - 1)) * r) atTop atTop :=
          tendsto_id.const_mul_atTop (by positivity)
        refine tendsto_neg_atTop_atBot.comp (this.congr fun r => ?_)
        ring
      simpa using (Real.tendsto_exp_atBot.comp h1).mul_const (weight p)
    · filter_upwards [eventually_ge_atTop 0] with r hr p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (weight_nonneg p))]
      exact term_le M r (mul_nonneg hM.le hr) p
  unfold kernel
  simpa using hlim.const_mul 4

end GppPrimeHaloKernel
