import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# The critical arithmetic OS Gram is positive, untruncated

Source: Codex, 2026-10-11, OS/KMS transport note (GPP-bridge
`work/codex/2026-10-11_os_kms_critical_arithmetic_transport.md`, §§1, J–K; PR #11 comments
6106986739 and 6107077019).

On `ℓ²(ℕ)` with `H|n⟩ = (log n)|n⟩`, the formal critical vector `v₀(n) = n^{−1/2}` is not in
`ℓ²`. For every `t > 0`, though, `v_t = e^{−tH}v₀`, i.e. `v_t(n) = n^{−1/2−t}`, is in `ℓ²`.
So `⟨v_t, v_u⟩ = Σₙ n^{−1−t−u} = ζ(1+t+u)` is an honest, **untruncated** Osterwalder–Schrader
kernel on positive times.

* `gram_eq`: for any weights `wₙ`, the finite reflected form
  `Σᵢⱼ cᵢcⱼ Σₙ wₙ n^{−tᵢ} n^{−tⱼ}` equals `Σₙ wₙ (Σᵢ cᵢ n^{−tᵢ})²`, given summability.
* `gram_nonneg`: hence it is `≥ 0` when `wₙ ≥ 0`.
* `critical_summable` and `critical_gram_nonneg`: the critical weight `wₙ = 1/n`, with
  every `tᵢ > 0`, satisfies the hypotheses. So the matrix `[Σₙ n^{−1−tᵢ−tⱼ}]`, which is
  `[ζ(1+tᵢ+tⱼ)]`, is positive semidefinite with no prime truncation and no hypothesis on
  zeros.

The same `gram_eq` covers Codex's thermal prime-power Gram with weights `Λ(m) m^{−β}`,
given its summability.

Scope: this kernel is **not** the completed `ξ` heat trace `K(t)`. Positivity of the
completed difference (Archimedean minus primes) is RH-strength and is not claimed here.
The positive-time restriction is essential: `v₀ ∉ ℓ²`. No RH claim.
-/

namespace GppCriticalRiggedGram

open Finset

variable {ι : Type*}

theorem gram_eq (w : ℕ → ℝ) (s : Finset ι) (c t : ι → ℝ)
    (hsum : ∀ i ∈ s, ∀ j ∈ s,
      Summable (fun n : ℕ => w n * (n : ℝ) ^ (-t i) * (n : ℝ) ^ (-t j))) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * ∑' n : ℕ, w n * (n : ℝ) ^ (-t i) * (n : ℝ) ^ (-t j) =
      ∑' n : ℕ, w n * (∑ i ∈ s, c i * (n : ℝ) ^ (-t i)) ^ 2 := by
  have hexp : ∀ n : ℕ, w n * (∑ i ∈ s, c i * (n : ℝ) ^ (-t i)) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * (w n * (n : ℝ) ^ (-t i) * (n : ℝ) ^ (-t j)) := by
    intro n
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [Summable.tsum_finsetSum (fun i hi => summable_sum fun j hj => (hsum i hi j hj).mul_left _)]
  refine sum_congr rfl fun i hi => ?_
  rw [Summable.tsum_finsetSum (fun j hj => (hsum i hi j hj).mul_left _)]
  refine sum_congr rfl fun j hj => ?_
  rw [tsum_mul_left]

theorem gram_nonneg (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (s : Finset ι) (c t : ι → ℝ)
    (hsum : ∀ i ∈ s, ∀ j ∈ s,
      Summable (fun n : ℕ => w n * (n : ℝ) ^ (-t i) * (n : ℝ) ^ (-t j))) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * ∑' n : ℕ, w n * (n : ℝ) ^ (-t i) * (n : ℝ) ^ (-t j) := by
  rw [gram_eq w s c t hsum]
  exact tsum_nonneg fun n => mul_nonneg (hw n) (sq_nonneg _)

/-- The critical weight `1/n` at positive times: `Σₙ n^{−1} n^{−t} n^{−u}` converges. -/
theorem critical_summable {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Summable (fun n : ℕ => (n : ℝ)⁻¹ * (n : ℝ) ^ (-t) * (n : ℝ) ^ (-u)) := by
  have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + t + u))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine hp.congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : (1 + t + u) ≠ 0)]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.rpow_neg hn'.le, mul_assoc, ← Real.rpow_add hn', ← Real.rpow_neg_one,
      ← Real.rpow_add hn']
    ring_nf

/-- **Critical OS positivity, untruncated.** For positive times `tᵢ` the matrix
`[Σₙ n^{−1−tᵢ−tⱼ}] = [ζ(1+tᵢ+tⱼ)]` is positive semidefinite. -/
theorem critical_gram_nonneg (s : Finset ι) (c t : ι → ℝ) (ht : ∀ i ∈ s, 0 < t i) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      c i * c j * ∑' n : ℕ, (n : ℝ)⁻¹ * (n : ℝ) ^ (-t i) * (n : ℝ) ^ (-t j) :=
  gram_nonneg (fun n => (n : ℝ)⁻¹) (fun n => inv_nonneg.mpr (Nat.cast_nonneg n)) s c t
    (fun i hi j hj => critical_summable (ht i hi) (ht j hj))

end GppCriticalRiggedGram
