/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# `toeplitz_on_ker_cosh` for the actual form: what "prove or kill" reduces to

Turbo (PR #11, 6816810382) asked, for the **actual** ζ Weil form, to prove or kill
`T ≥ 2ℓ_s²` on `ker ℓ_c` (with `Q = T + 2ℓ_c² − 2ℓ_s²`, `T` = archimedean − prime truncated
convolution, `ℓ_c`, `ℓ_s` = pairings with `cosh(x/2)`, `sinh(x/2)`), with no zeros as input.

Here `Q` is any real function on a real vector space and `T` is *defined* from `Q` by the
rank-two identity, which is exactly how `T` sits inside the ζ form. Everything is PROVED and
purely algebraic:

* `claim_iff_hyperplane`: the claim at window `L` is **literally** `Q ≥ 0` on the hyperplane
  `ker ℓ_c`. The `−2ℓ_s²` cancels identically; the Toeplitz part carries no information beyond
  `Q` restricted to `ker ℓ_c`.
* `claim_of_arp`: ARP at `L` ⇒ claim at `L`.
* `arp_failure_of_not_claim`: a counterexample at window `L` *is* a vector with `Q < 0`, i.e. an
  ARP failure at `L`. So a "clean kill at a named window" exists only if RH is false.
* `no_negative_plane_of_claim`: claim ⇒ `Q` has at most one negative square (for `Q` the
  diagonal of a bilinear form): no 2-plane is negative definite.
* `claim_not_arp` (counterexample): the claim is strictly weaker than ARP algebraically.
* `one_neg_square_not_claim` (counterexample): "`T` has at most one negative square" does NOT
  imply the claim; the two formulations in the question are not equivalent, the claim is
  strictly stronger.
* `even_sector`: on even vectors (`ℓ_s = 0`) the claim is `T_even ≥ 0` on `ker ℓ_c`, again the
  same as `Q_even ≥ 0` there.
-/

namespace GppToeplitzHyperplane

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Toeplitz part, defined from the full form by `Q = T + 2ℓ_c² − 2ℓ_s²`. -/
def toep (Q : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) (v : E) : ℝ :=
  Q v - 2 * (lc v) ^ 2 + 2 * (ls v) ^ 2

/-- Turbo's claim at one window: `T ≥ 2ℓ_s²` on `ker ℓ_c`. -/
def Claim (Q : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ v, lc v = 0 → 2 * (ls v) ^ 2 ≤ toep Q lc ls v

theorem claim_iff_hyperplane (Q : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) :
    Claim Q lc ls ↔ ∀ v, lc v = 0 → 0 ≤ Q v := by
  unfold Claim toep
  refine forall_congr' fun v => imp_congr_right fun hv => ?_
  rw [hv]; constructor <;> intro h <;> nlinarith

theorem claim_of_arp (Q : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) (h : ∀ v, 0 ≤ Q v) :
    Claim Q lc ls :=
  (claim_iff_hyperplane Q lc ls).2 fun v _ => h v

theorem arp_failure_of_not_claim (Q : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) (h : ¬ Claim Q lc ls) :
    ∃ v, lc v = 0 ∧ Q v < 0 := by
  rw [claim_iff_hyperplane] at h
  push Not at h
  exact h

theorem even_sector (Q : E → ℝ) (lc ls : E →ₗ[ℝ] ℝ) {v : E} (hs : ls v = 0) (hc : lc v = 0) :
    0 ≤ toep Q lc ls v ↔ 0 ≤ Q v := by
  unfold toep; rw [hs, hc]; constructor <;> intro h <;> nlinarith

/-- Claim ⇒ at most one negative square: no two vectors span a negative-definite plane. -/
theorem no_negative_plane_of_claim (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (lc ls : E →ₗ[ℝ] ℝ)
    (h : Claim (fun v => B v v) lc ls) (u w : E) :
    ¬ (∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → B (a • u + b • w) (a • u + b • w) < 0) := by
  intro hneg
  rw [claim_iff_hyperplane] at h
  by_cases hz : lc w = 0 ∧ lc u = 0
  · have := hneg 1 0 (Or.inl one_ne_zero)
    simp only [one_smul, zero_smul, add_zero] at this
    exact absurd (h u hz.2) (not_le.2 this)
  · have hab : lc w ≠ 0 ∨ -lc u ≠ 0 := by
      by_contra hc; push Not at hc; exact hz ⟨hc.1, neg_eq_zero.1 hc.2⟩
    have hk : lc (lc w • u + (-lc u) • w) = 0 := by
      simp only [map_add, map_smul, smul_eq_mul]; ring
    exact absurd (h _ hk) (not_le.2 (hneg _ _ hab))

/-- The claim does not imply ARP: on `ℝ × ℝ`, `Q = −x² + y²`, `ℓ_c = x`, `ℓ_s = 0`. -/
theorem claim_not_arp :
    Claim (fun p : ℝ × ℝ => -p.1 ^ 2 + p.2 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 ∧
      ¬ ∀ p : ℝ × ℝ, 0 ≤ -p.1 ^ 2 + p.2 ^ 2 := by
  refine ⟨(claim_iff_hyperplane _ _ _).2 fun p hp => ?_, fun h => ?_⟩
  · simp only [LinearMap.fst_apply] at hp; rw [hp]; nlinarith [sq_nonneg p.2]
  · have := h (1, 0); norm_num at this

/-- "`T` has at most one negative square" does not imply the claim: `Q = 3x² − y²`,
`ℓ_c = x`, `ℓ_s = 0` gives `T = x² − y²` (exactly one negative square) but `T(0,1) = −1 < 0`
on `ker ℓ_c`. -/
theorem one_neg_square_not_claim :
    (toep (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - p.2 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 =
        fun p => p.1 ^ 2 - p.2 ^ 2) ∧
      ¬ Claim (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - p.2 ^ 2) (LinearMap.fst ℝ ℝ ℝ) 0 := by
  refine ⟨funext fun p => ?_, fun h => ?_⟩
  · simp [toep]; ring
  · have := h (0, 1) (by simp)
    simp [toep] at this; norm_num at this

end GppToeplitzHyperplane

#print axioms GppToeplitzHyperplane.claim_iff_hyperplane
#print axioms GppToeplitzHyperplane.claim_of_arp
#print axioms GppToeplitzHyperplane.arp_failure_of_not_claim
#print axioms GppToeplitzHyperplane.even_sector
#print axioms GppToeplitzHyperplane.no_negative_plane_of_claim
#print axioms GppToeplitzHyperplane.claim_not_arp
#print axioms GppToeplitzHyperplane.one_neg_square_not_claim
