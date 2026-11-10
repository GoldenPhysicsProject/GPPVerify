/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.LogDerivativeLandau
import GppVerify.Upstream.AvoidFiniteSet
import GppVerify.RiemannHypothesis.XiZeroCounting
import GppVerify.RiemannHypothesis.XiOrder

/-!
# Explicit formula, stage E4b: a polynomial bound for `ξ'/ξ` at good heights

For every `T ≥ 1` there is a height `t ∈ [T, T+1]` such that `ξ` has no zero on the horizontal
segment `{σ + i t : -1 ≤ σ ≤ 2}` and `‖ξ'/ξ‖` is at most a fixed power of `t` on it.
-/

open Complex Metric Set

namespace GppXiZeroCounting

open GppLogDerivZeroFree

/-- A zero of `ξ` has order at least one. -/
theorem one_le_orderNat_xi {u : ℂ} (h : xi u = 0) : 1 ≤ analyticOrderNatAt xi u := by
  have hne0 : analyticOrderAt xi u ≠ 0 := by
    rw [Ne, (differentiable_xi.analyticAt u).analyticOrderAt_eq_zero]
    simpa using h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_xi_ne_top u)
  unfold analyticOrderNatAt
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  have : n ≠ 0 := fun h => hne0 (by simp [h])
  omega

/-- A point of `closedBall 0 r` is in the support of the divisor of `ξ` iff it is a zero. -/
theorem mem_support_divisor_xi_iff {r : ℝ} {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) r) :
    u ∈ Function.support (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)) ↔ xi u = 0 := by
  rw [Function.mem_support, divisor_xi_apply hu]
  constructor
  · intro h
    by_contra hx
    apply h
    have : analyticOrderAt xi u = 0 := (differentiable_xi.analyticAt u).analyticOrderAt_eq_zero.2 hx
    simp [analyticOrderNatAt, this]
  · intro h
    have := one_le_orderNat_xi h
    omega

/-- The zeros of `ξ` in a closed ball form a finite set. -/
theorem finite_zeros_xi (r : ℝ) : {u : ℂ | ‖u‖ ≤ r ∧ xi u = 0}.Finite := by
  have hon : AnalyticOnNhd ℂ xi (closedBall (0 : ℂ) r) := fun z _ => differentiable_xi.analyticAt z
  have hfin := (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall 0 r)
  refine hfin.subset ?_
  rintro u ⟨hu, hx⟩
  have hu' : u ∈ closedBall (0 : ℂ) r := by simpa using hu
  exact (mem_support_divisor_xi_iff hu').2 hx

/-- **A radius in `[R₀, R₀ + 1]` such that `ξ` has no zero on the circle.** -/
theorem exists_radius_no_zero (R₀ : ℝ) :
    ∃ R ∈ Icc R₀ (R₀ + 1), ∀ z : ℂ, ‖z‖ = R → xi z ≠ 0 := by
  have hfin : (norm '' {u : ℂ | ‖u‖ ≤ R₀ + 1 ∧ xi u = 0}).Finite := (finite_zeros_xi _).image _
  have hinf : (Icc R₀ (R₀ + 1)).Infinite := Icc_infinite (by linarith)
  obtain ⟨R, hR, hnot⟩ := hinf.exists_notMem_finset hfin.toFinset
  refine ⟨R, hR, fun z hz hx => hnot ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨z, ⟨by rw [hz]; exact hR.2, hx⟩, hz⟩

end GppXiZeroCounting
