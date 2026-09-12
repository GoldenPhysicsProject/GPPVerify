import GppVerify.RiemannHypothesis.HeatTraceCriterion

/-!
# The Hilbert-Pólya heat trace is completely monotone, and why that is RH

`arithmetic_principal_series_RH_program` proves `RH <=> K completely monotone on (0,∞)`,
where `K(t) = (4πt)^{-1/2} <W, exp(-x²/4t)>` and `W = ν∞ - ν_p`, and observes that under
RH this is literally the Hilbert-Pólya heat trace `K(t) = Σ_{γ>0} m_γ exp(-γ² t)`.

This file formalizes the forward half at the level of the mode expansion: **a nonnegative
superposition of heat modes is completely monotone.** The arithmetic content is where the
`γ² ≥ 0` comes from. If `ρ = 1/2 + iγ` with `γ` REAL, then `γ² ≥ 0` and the mode
`exp(-γ² t)` decays, so `completelyMonotone_exp_neg` applies. An off-critical-line zero has
`γ` complex, `γ²` is then not a nonnegative real, and the mode is not completely monotone.
**Complete monotonicity of the heat trace is exactly the statement that every `γ` is real.**
That is the mechanism behind the paper's equivalence, and it is what this file makes explicit.

## The bridge to Weil positivity, and the one piece Mathlib is missing

The same statement reaches the Weil side through Bochner plus Gaussian self-duality:

  W positive-type  =>  W = Fourier transform of a positive measure ν   (Bochner)
  <W, exp(-x²/4t)> = ∫ (gaussian)^ (ξ) dν(ξ) = √(4πt) ∫ exp(-t ξ²) dν(ξ)
  K(t) = ∫ exp(-λ t) dμ(λ),  μ = pushforward of ν under ξ ↦ ξ², positive
  => K completely monotone.

So Weil positivity and heat-trace complete monotonicity are the same condition, and the
Gaussian being its own Fourier transform is precisely why the HEAT kernel is the right
subordinator rather than some other one. The measure-level version needs Bochner's theorem,
which is not in Mathlib at the pinned commit; the CONVERSE (completely monotone => Laplace
transform of a measure) is Bernstein-Widder, also absent. The finite/discrete case proved
below needs neither.
-/

namespace GppHeatTrace

open Finset

/-- The smooth family of heat modes, at every finite smoothness index. -/
theorem contDiff_expMode (a : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun t : ℝ => Real.exp (-a * t)) := by fun_prop

theorem contDiff_heatMode (m a : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun t : ℝ => m * Real.exp (-a * t)) := by fun_prop

/-- Complete monotonicity is preserved by nonnegative scaling of a heat mode. -/
theorem completelyMonotone_heatMode {m a : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) :
    CompletelyMonotone (fun t => m * Real.exp (-a * t)) := by
  intro n t ht
  rw [iteratedDeriv_const_mul m ((contDiff_expMode a).contDiffAt (x := t))]
  have := completelyMonotone_exp_neg ha n t ht
  nlinarith [this]

/-- **The Hilbert-Pólya heat trace is completely monotone.** A finite nonnegative
    superposition of modes `exp(-γ² t)` is completely monotone, for any REAL ordinates `γ`.
    Realness of `γ` is the whole content: it is what makes `γ² ≥ 0`. An off-critical-line
    zero gives a `γ` that is not real, `γ²` is then not a nonnegative real, and the mode is
    not completely monotone. -/
theorem completelyMonotone_heatTrace {ι : Type*} (s : Finset ι) (m γ : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) :
    CompletelyMonotone (fun t => ∑ i ∈ s, m i * Real.exp (-(γ i ^ 2) * t)) := by
  classical
  induction s using Finset.induction with
  | empty => intro n t _; simp [CompletelyMonotone, iteratedDeriv_const]
  | insert a s ha ih =>
      intro n t ht
      have hhead := completelyMonotone_heatMode (hm a (Finset.mem_insert_self a s))
        (by positivity : (0:ℝ) ≤ γ a ^ 2) n t ht
      have htail := ih (fun i hi => hm i (Finset.mem_insert_of_mem hi)) n t ht
      have hsum : (fun t : ℝ => ∑ i ∈ insert a s, m i * Real.exp (-(γ i ^ 2) * t))
          = (fun t : ℝ => m a * Real.exp (-(γ a ^ 2) * t))
              + (fun t : ℝ => ∑ i ∈ s, m i * Real.exp (-(γ i ^ 2) * t)) := by
        funext t; simp [Finset.sum_insert ha]
      rw [hsum, iteratedDeriv_add (contDiff_heatMode (m a) (γ a ^ 2)).contDiffAt
        (ContDiff.sum (fun i _ => contDiff_heatMode (m i) (γ i ^ 2))).contDiffAt]
      nlinarith [hhead, htail]

end GppHeatTrace
