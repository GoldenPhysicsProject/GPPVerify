/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import GppVerify.RiemannHypothesis.XiZeroCounting
import GppVerify.RiemannHypothesis.CelestialNodal

/-!
# Explicit formula, stage E3b (part 2): symmetry of the zero multiplicities

The nontrivial zeros of `ζ`, with multiplicity, are invariant under `ρ ↦ conj ρ` (reality of `ξ`)
and `ρ ↦ 1 - ρ` (functional equation), hence under `ρ ↦ 1 - conj ρ`.
-/

open Complex

namespace GppXiZeroCounting

open GppLogDerivZeroFree

/-- One direction: if `ξ` has order `n` at `z`, it has order `n` at `conj z`. -/
theorem analyticOrderAt_xi_conj_of_eq {z : ℂ} {n : ℕ} (h : analyticOrderAt xi z = n) :
    analyticOrderAt xi (starRingEnd ℂ z) = n := by
  have hxi : AnalyticAt ℂ xi z := differentiable_xi.analyticAt z
  obtain ⟨g, hg, hgz, hev⟩ := (hxi.analyticOrderAt_eq_natCast).1 h
  have hxi' : AnalyticAt ℂ xi (starRingEnd ℂ z) := differentiable_xi.analyticAt _
  refine (hxi'.analyticOrderAt_eq_natCast).2 ?_
  refine ⟨fun s => starRingEnd ℂ (g (starRingEnd ℂ s)), ?_, ?_, ?_⟩
  · rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hd := Complex.analyticAt_iff_eventually_differentiableAt.1 hg
    have hcont : Filter.Tendsto (starRingEnd ℂ) (nhds (starRingEnd ℂ z)) (nhds z) := by
      simpa using (continuous_conj.tendsto (starRingEnd ℂ z))
    filter_upwards [hcont.eventually hd] with s hs
    have hs' : DifferentiableAt ℂ g (starRingEnd ℂ s) := hs
    simpa [Function.comp_def] using hs'.conj_conj
  · simpa using hgz
  · have hcont : Filter.Tendsto (starRingEnd ℂ) (nhds (starRingEnd ℂ z)) (nhds z) := by
      simpa using (continuous_conj.tendsto (starRingEnd ℂ z))
    filter_upwards [hcont.eventually hev] with s hs
    have h1 : xi s = starRingEnd ℂ (xi (starRingEnd ℂ s)) := by
      rw [GppCelestialNodal.xi_conj]; simp
    rw [h1, hs]
    simp [map_mul, map_pow]

theorem analyticOrderAt_xi_conj (z : ℂ) :
    analyticOrderAt xi (starRingEnd ℂ z) = analyticOrderAt xi z := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_xi_ne_top z)
  rw [← hn]
  exact analyticOrderAt_xi_conj_of_eq hn.symm

/-- The functional equation `ξ(1 - s) = ξ(s)` makes the order symmetric about `1/2`. -/
theorem analyticOrderAt_xi_one_sub (z : ℂ) :
    analyticOrderAt xi (1 - z) = analyticOrderAt xi z := by
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := by fun_prop
  have hd : deriv (fun s : ℂ => 1 - s) z ≠ 0 := by simp
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg hd
  have hcomp : xi ∘ (fun s : ℂ => 1 - s) = xi := funext fun s => xi_one_sub s
  rw [hcomp] at this
  exact this.symm

theorem conj_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ GppWeilCriterion.nontrivialZeros) :
    starRingEnd ℂ ρ ∈ GppWeilCriterion.nontrivialZeros := by
  obtain ⟨hz, h0, h1⟩ := hρ
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  rw [GppRH.riemannZeta_conj, hz, map_zero]

/-- **Symmetry of the zero data.** The nontrivial zeros and their multiplicities are invariant
under `ρ ↦ 1 - conj ρ` and `ρ ↦ conj ρ`. -/
theorem zeroData_symmetric {ρ : ℂ} (hρ : ρ ∈ GppWeilCriterion.nontrivialZeros) :
    GppWeilCriterion.zetaInvolution ρ ∈ GppWeilCriterion.nontrivialZeros ∧
      zeroMult (GppWeilCriterion.zetaInvolution ρ) = zeroMult ρ ∧
      starRingEnd ℂ ρ ∈ GppWeilCriterion.nontrivialZeros ∧
      zeroMult (starRingEnd ℂ ρ) = zeroMult ρ := by
  have hι := GppWeilCriterion.nontrivialZeros_mem_involution hρ
  have hc := conj_mem_nontrivialZeros hρ
  refine ⟨hι, ?_, hc, ?_⟩
  · rw [zeroMult_eq_orderNat_xi hι, zeroMult_eq_orderNat_xi hρ]
    unfold analyticOrderNatAt GppWeilCriterion.zetaInvolution
    rw [analyticOrderAt_xi_one_sub, analyticOrderAt_xi_conj]
  · rw [zeroMult_eq_orderNat_xi hc, zeroMult_eq_orderNat_xi hρ]
    unfold analyticOrderNatAt
    rw [analyticOrderAt_xi_conj]

end GppXiZeroCounting
