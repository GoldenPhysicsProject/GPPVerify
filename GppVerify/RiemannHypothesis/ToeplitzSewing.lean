/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# The minimal zero-free sewing hypothesis for `Q ≥ 0` on `ker ℓ_c`

Turbo (PR #11, 6817261425): name the minimal zero-free sewing hypothesis `H` (exact Prop,
named premises only) with `H ⇒ Q ≥ 0` on `ker ℓ_c`, `H` not ARP-equivalent by construction;
test `H` against `claim_not_arp` and `one_neg_square_not_claim`, or show no such `H` exists
short of ARP.

Named premises: `A` (archimedean form), `P` (prime / truncated convolution form), `ℓ_c`, `ℓ_s`
(pairings with `cosh(x/2)`, `sinh(x/2)`), with `Q = A − P + 2ℓ_c² − 2ℓ_s²`. No zeros appear.

* `SewingH A P ℓ_c ℓ_s`: `P + 2ℓ_s² ≤ A` on `ker ℓ_c` (archimedean dominates prime plus the odd
  pole term on the cosh-hyperplane).
* `sewingH_iff_claim` (PROVED): `SewingH ↔ Q ≥ 0 on ker ℓ_c`.
* `sewingH_minimal` (PROVED): every hypothesis that implies the claim implies `SewingH`;
  so `SewingH` is the weakest such `H` (it is the claim, rewritten in the named pieces).
* `sewingH_test_claim_not_arp` (PROVED): on the `claim_not_arp` datum `SewingH` holds and ARP
  fails, so `SewingH` is not ARP-equivalent by construction.
* `sewingH_test_one_neg_square` (PROVED): on the `one_neg_square_not_claim` datum `SewingH`
  fails, as it must.
* `arp_iff_affine` (PROVED): for a bilinear form, ARP ⇔ `Q ≥ 0` on the affine hyperplane
  `ℓ_c = 1`. The linear hyperplane `ker ℓ_c` is recovered from the affine one by a limit, so
  the whole content of ARP beyond `SewingH` lives off `ker ℓ_c`, and positivity off `ker ℓ_c`
  alone already gives ARP.
-/

namespace GppToeplitzSewing

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The full form assembled from named pieces. -/
def weilQ (A P : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) (v : E) : ℝ :=
  A v - P v + 2 * (lc v) ^ 2 - 2 * (ls v) ^ 2

/-- Positivity of `Q` on `ker ℓ_c` (Turbo's claim, hyperplane form). -/
def HyperClaim (Q : E → ℝ) (lc : E →ₗ[ℝ] ℝ) : Prop := ∀ v, lc v = 0 → 0 ≤ Q v

/-- The sewing hypothesis: archimedean dominates prime plus odd pole on `ker ℓ_c`. -/
def SewingH (A P : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ v, lc v = 0 → P v + 2 * (ls v) ^ 2 ≤ A v

theorem sewingH_iff_claim (A P : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) :
    SewingH A P lc ls ↔ HyperClaim (weilQ A P lc ls) lc := by
  unfold SewingH HyperClaim weilQ
  refine forall_congr' fun v => imp_congr_right fun hv => ?_
  rw [hv]; constructor <;> intro h <;> nlinarith

/-- Minimality: any hypothesis on the pieces that yields the claim yields `SewingH`. -/
theorem sewingH_minimal (H : (E → ℝ) → (E → ℝ) → Prop) (lc ls : E →ₗ[ℝ] ℝ)
    (hH : ∀ A P, H A P → HyperClaim (weilQ A P lc ls) lc) (A P : E → ℝ) (h : H A P) :
    SewingH A P lc ls :=
  (sewingH_iff_claim A P lc ls).2 (hH A P h)

/-- Test 1 (`claim_not_arp` datum `Q = −x² + y²`, `ℓ_c = x`, `ℓ_s = 0`), split as
`A = y²`, `P = 3x²`: `SewingH` holds, ARP fails. -/
theorem sewingH_test_claim_not_arp :
    SewingH (fun p : ℝ × ℝ => p.2 ^ 2) (fun p => 3 * p.1 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 ∧
      (weilQ (fun p : ℝ × ℝ => p.2 ^ 2) (fun p => 3 * p.1 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 =
        fun p => -p.1 ^ 2 + p.2 ^ 2) ∧
      ¬ ∀ p : ℝ × ℝ,
        0 ≤ weilQ (fun p : ℝ × ℝ => p.2 ^ 2) (fun p => 3 * p.1 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 p := by
  refine ⟨fun p hp => ?_, funext fun p => ?_, fun h => ?_⟩
  · simp only [LinearMap.fst_apply] at hp
    simp only [LinearMap.zero_apply, hp]; nlinarith [sq_nonneg p.2]
  · simp [weilQ]; ring
  · have := h (1, 0); simp [weilQ] at this; norm_num at this

/-- Test 2 (`one_neg_square_not_claim` datum `Q = 3x² − y²`, `ℓ_c = x`, `ℓ_s = 0`), split as
`A = x²`, `P = y²`: `SewingH` fails. -/
theorem sewingH_test_one_neg_square :
    (weilQ (fun p : ℝ × ℝ => p.1 ^ 2) (fun p => p.2 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 =
        fun p => 3 * p.1 ^ 2 - p.2 ^ 2) ∧
      ¬ SewingH (fun p : ℝ × ℝ => p.1 ^ 2) (fun p => p.2 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 := by
  refine ⟨funext fun p => ?_, fun h => ?_⟩
  · simp [weilQ]; ring
  · have := h (0, 1) (by simp); norm_num at this

/-- A real quadratic `a + bε + cε²` that is `≥ 0` for every `ε ≠ 0` has `a ≥ 0`. -/
theorem quad_const_nonneg (a b c : ℝ) (h : ∀ ε : ℝ, ε ≠ 0 → 0 ≤ a + b * ε + c * ε ^ 2) :
    0 ≤ a := by
  by_contra ha
  push Not at ha
  set M := |b| + |c| + 1 with hM
  have hMpos : 0 < M := by positivity
  set ε := min 1 (-a / (2 * M)) with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ -a / (2 * M) := min_le_right _ _
  have hεM : ε * M ≤ -a / 2 := by
    have := mul_le_mul_of_nonneg_right hε2 hMpos.le
    rw [div_mul_eq_mul_div, mul_comm 2 M, ← div_div, mul_div_assoc, div_self hMpos.ne',
      mul_one] at this
    linarith
  have hb : b * ε ≤ |b| * ε := mul_le_mul_of_nonneg_right (le_abs_self b) hεpos.le
  have hc : c * ε ^ 2 ≤ |c| * ε := by
    have h1 : c * ε ^ 2 ≤ |c| * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (sq_nonneg ε)
    have h2 : |c| * ε ^ 2 ≤ |c| * ε := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg c); nlinarith
    linarith
  have := h ε hεpos.ne'
  nlinarith [abs_nonneg b, abs_nonneg c]

/-- ARP ⇔ positivity on the affine hyperplane `ℓ_c = 1` (bilinear `B`, any `v₀` with
`ℓ_c v₀ = 1`). -/
theorem arp_iff_affine (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (lc : E →ₗ[ℝ] ℝ) (v₀ : E) (h₀ : lc v₀ = 1) :
    (∀ v, 0 ≤ B v v) ↔ ∀ k, lc k = 0 → 0 ≤ B (v₀ + k) (v₀ + k) := by
  constructor
  · intro h k _; exact h _
  · intro h
    -- off the hyperplane: scale
    have off : ∀ v, lc v ≠ 0 → 0 ≤ B v v := by
      intro v hv
      set t := lc v with ht
      have hk : lc (t⁻¹ • v - v₀) = 0 := by
        simp only [map_sub, map_smul, smul_eq_mul, h₀]
        rw [inv_mul_cancel₀ hv, sub_self]
      have hv' : v = t • (v₀ + (t⁻¹ • v - v₀)) := by
        rw [add_sub_cancel, smul_smul, mul_inv_cancel₀ hv, one_smul]
      have := h _ hk
      rw [hv']
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      nlinarith [sq_nonneg t]
    intro v
    by_cases hv : lc v = 0
    · apply quad_const_nonneg (B v v) (B v v₀ + B v₀ v) (B v₀ v₀)
      intro ε hε
      have hw : lc (v + ε • v₀) ≠ 0 := by simp [hv, h₀, hε]
      have := off _ hw
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul] at this
      nlinarith
    · exact off v hv

/-- Algebra of one off-line zero quadruple `{γ, −γ, γ̄, −γ̄}` (`Re γ ≠ 0`): for real `f`
its explicit-formula contribution is `4 Re(F(γ)F(−γ))`; in real coordinates
`a = F(γ) = a₁ + i a₂`, `b = F(−γ) = b₁ + i b₂` this is `4(a₁b₁ − a₂b₂)`, which is negative
definite on the plane `a₁ = s, b₁ = −s, a₂ = b₂ = t`. Hence such a block carries two negative
squares, which `no_negative_plane_of_claim` forbids once it is localised (GAP, see notes). -/
theorem quadruple_block_neg_plane (s t : ℝ) (h : s ≠ 0 ∨ t ≠ 0) :
    4 * (s * (-s) - t * t) < 0 := by
  rcases h with h | h
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg t]
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg s]

end GppToeplitzSewing

#print axioms GppToeplitzSewing.sewingH_iff_claim
#print axioms GppToeplitzSewing.sewingH_minimal
#print axioms GppToeplitzSewing.sewingH_test_claim_not_arp
#print axioms GppToeplitzSewing.sewingH_test_one_neg_square
#print axioms GppToeplitzSewing.quad_const_nonneg
#print axioms GppToeplitzSewing.arp_iff_affine
#print axioms GppToeplitzSewing.quadruple_block_neg_plane
