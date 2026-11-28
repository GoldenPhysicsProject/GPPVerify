/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.NymanBeurlingBoundStates

/-!
# The arithmetic bulk state of the one-dimensional ACFT is normalizable

Pasterski–Shao (arXiv:1705.01027, (3.6)–(3.9), (4.7)–(4.9)) build the
celestial basis in two steps: a *normalizable* bulk state (a plane wave
packet, normalizable in the Klein–Gordon pairing), and its expansion in
conformal primaries on the principal series `Δ ∈ d/2 + iℝ`.

In the one-dimensional arithmetic CFT (`d = 1`, `Δ = s`, no halving) the
Hilbert space is `L²((0, ∞), dx)`, the principal series is `Re s = 1/2`
(`GppMellinPlancherelL2`), and the arithmetic bulk state is
`χ(x) = {1/x}` (`GppNymanBeurling.fracInv`), the counting profile of the
integers seen from the boundary.

This file proves the first half of that chain for `χ`:

* `fracInv_eq_inv_of_one_lt` — on `x > 1`, `χ(x) = 1/x`.
* `memLp_fracInv_two` — **PROVED.** `χ ∈ L²((0, ∞), dx)`: the arithmetic
  state is a genuine (normalizable) vector of the `d = 1` theory, unlike
  the individual conformal primaries `x^{s-1}`, which never are.
* `principal_coefficient_fracInv` — **PROVED** (re-export of
  `mellin_fracInv` on the line): its conformal-primary coefficient at the
  principal weight `s = 1/2 + iτ` is `-ζ(s)/s`, an absolutely convergent
  Mellin integral.

So the nodes of the arithmetic state in the principal-series basis are
exactly the critical-line zeros of `ζ`. Nothing here says anything about
zeros off the line: there `x^{s-1}` is not a principal-series primary,
and placing such a zero is the open target named in
GPPDiscovery5 `experiments/acft_pasterski_shao/ACFT.md`. No zero of `ζ`
is used as an input.

— Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos /
Grok (GPPDiscovery5).
-/

set_option autoImplicit false

namespace GppACFTArithmeticState

open MeasureTheory Set Complex
open GppNymanBeurling

/-- On `x > 1` the arithmetic profile is the pure power `1/x`. -/
theorem fracInv_eq_inv_of_one_lt {x : ℝ} (hx : 1 < x) :
    fracInv x = ((x⁻¹ : ℝ) : ℂ) := by
  unfold fracInv
  have h0 : 0 ≤ x⁻¹ := inv_nonneg.2 (by linarith)
  have h1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  rw [Int.fract_eq_self.2 ⟨h0, h1⟩]

/-- **The arithmetic bulk state is normalizable.** `x ↦ {1/x}` lies in
`L²((0, ∞), dx)`. -/
theorem memLp_fracInv_two :
    MemLp fracInv 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable fracInv (volume.restrict (Ioi (0 : ℝ))) :=
    measurable_fracInv.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  change IntegrableOn (fun x => ‖fracInv x‖ ^ 2) (Ioi 0)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
    · simp [Real.volume_Ioc]
    · exact (measurable_fracInv.norm.pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h := norm_fracInv_le x
      have h0 : 0 ≤ ‖fracInv x‖ := norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
  · have hI : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine hI.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx1 : 1 < x := hx
    have hxpos : 0 < x := by linarith
    rw [fracInv_eq_inv_of_one_lt hx1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 hxpos.le)]
    show x ^ (-2 : ℝ) = x⁻¹ ^ 2
    rw [Real.rpow_neg hxpos.le, inv_pow]
    norm_num

/-- **Principal-series coefficients of the arithmetic state.** At every
principal weight `s = 1/2 + iτ`, the conformal-primary coefficient
`∫₀^∞ x^{s-1} χ(x) dx` of the arithmetic state is `-ζ(s)/s`. -/
theorem principal_coefficient_fracInv (τ : ℝ) :
    mellin fracInv ((1 / 2 : ℂ) + τ * I) =
      -riemannZeta ((1 / 2 : ℂ) + τ * I) / ((1 / 2 : ℂ) + τ * I) := by
  apply mellin_fracInv <;> norm_num

/-- The nodes of the arithmetic state in the principal-series basis are
exactly the critical-line zeros of `ζ`. -/
theorem principal_node_iff (τ : ℝ) :
    mellin fracInv ((1 / 2 : ℂ) + τ * I) = 0 ↔
      riemannZeta ((1 / 2 : ℂ) + τ * I) = 0 := by
  rw [principal_coefficient_fracInv]
  have hs : (1 / 2 : ℂ) + τ * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  constructor
  · intro h
    rcases div_eq_zero_iff.1 h with h | h
    · exact neg_eq_zero.1 h
    · exact absurd h hs
  · intro h; rw [h, neg_zero, zero_div]

end GppACFTArithmeticState

#print axioms GppACFTArithmeticState.memLp_fracInv_two
#print axioms GppACFTArithmeticState.principal_coefficient_fracInv
#print axioms GppACFTArithmeticState.principal_node_iff
