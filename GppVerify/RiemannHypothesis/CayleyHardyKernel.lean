import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Basic

/-!
# The zeta pole and the Hardy kernel, through the Cayley transform

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-27_zeta_pole_forces_su11_half_hardy_kernel.md` (commit `f914bc0`) and its
checker `DiscoveryLean/CayleyHardyKernel.lean` (`0333aab`).

Centre the Dirichlet–Hardy kernel at the critical line: with `s = ½ + z` and `w = ½ + η`
(`Re z, Re η > 0`), the kernel is `K(z, η) = ζ(1 + z + η̄)`. The note makes three claims.

1. **The pole gives the half-plane Hardy kernel.** `ζ(1+q) = 1/q + γ + O(q)`, so
   `K(z, η) = 1/(z + η̄) + (regular)`. The singular part `1/(z + η̄)` is the Szegő kernel of
   `H²` of the right half-plane, up to the normalizing constant.
2. **Cayley transform.** With `z = (1+u)/(1−u)` and `η = (1+v)/(1−v)`,
   `z + η̄ = 2(1 − u v̄)/((1−u)(1−v̄))`, so `1/(z + η̄) = ((1−u)(1−v̄)/2) · (1 − u v̄)^{-1}`.
3. **Weight.** The disc kernel `(1 − u v̄)^{-1}` is the case `2k = 1` of the `SU(1,1)` lowest-weight
   kernel `(1 − u v̄)^{-2k}`.

This file proves 1 and 2 over `ℂ`. Codex's checker proved the real-variable rational identity
only. Here the conjugations are carried explicitly, and the half-plane/disc correspondence
is proved as well:

* `re_cayley`: `Re((1+u)/(1−u)) = (1 − |u|²)/|1−u|²`, so `re_cayley_pos_iff`:
  `Re z > 0 ↔ |u| < 1`. The Cayley map really does carry the disc onto the right half-plane
  used in the note.
* `cayley_add_conj`, `cayley_kernel`: the identity of claim 2.
* `one_sub_mul_conj_ne_zero`: the disc kernel has no pole on the open disc.
* `tendsto_zeta_one_add_sub_inv`: `ζ(1+q) − 1/q → γ` as `q → 0`. This is the exact form of
  claim 1: `K(z, η) − 1/(z + η̄) → γ` as `z + η̄ → 0`. It is Mathlib's
  `tendsto_riemannZeta_sub_one_div`, recentred.

## Scope

Claim 3 is a matching of kernel shapes: `(1−uv̄)^{-1}` has the form `(1−uv̄)^{-2k}` with `k = ½`.
The `SU(1,1)` representation theory behind the name is not formalized. Neither is the note's
further identification of this `k = ½` with the TFD oscillator, the Casimir threshold and the
Plancherel weight; the note itself calls those identifications structural. Nothing here uses
or implies information about zeros.
-/

open Filter Topology ComplexConjugate

namespace GppCayleyHardyKernel

/-- The Cayley map `u ↦ (1+u)/(1−u)`, disc to right half-plane. -/
noncomputable def cayley (u : ℂ) : ℂ := (1 + u) / (1 - u)

/-- `Re((1+u)/(1−u)) = (1 − |u|²)/|1−u|²`. -/
theorem re_cayley (u : ℂ) (hu : u ≠ 1) :
    (cayley u).re = (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
  have h1 : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  rw [cayley, Complex.div_re, ← add_div]
  congr 1
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im, Complex.normSq_apply]
  ring

/-- The Cayley map sends the open unit disc exactly onto the right half-plane. -/
theorem re_cayley_pos_iff (u : ℂ) (hu : u ≠ 1) :
    0 < (cayley u).re ↔ Complex.normSq u < 1 := by
  have h1 : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hpos : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.mpr h1
  rw [re_cayley u hu, div_pos_iff_of_pos_right hpos, sub_pos]

/-- **The Cayley identity for the Hardy kernel.**
`z + η̄ = 2(1 − u v̄)/((1−u)(1−v̄))` for `z = cayley u`, `η = cayley v`. -/
theorem cayley_add_conj (u v : ℂ) (hu : u ≠ 1) (hv : v ≠ 1) :
    cayley u + conj (cayley v) = 2 * (1 - u * conj v) / ((1 - u) * (1 - conj v)) := by
  have h1 : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h2 : (1 : ℂ) - conj v ≠ 0 := by
    rw [← map_one (starRingEnd ℂ), ← map_sub]
    exact (map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hv))
  rw [cayley, cayley, map_div₀, map_add, map_sub, map_one]
  field_simp
  ring

/-- **The half-plane Hardy kernel as a gauge factor times the disc kernel.**
`1/(z + η̄) = ((1−u)(1−v̄)/2) · (1 − u v̄)⁻¹`. -/
theorem cayley_kernel (u v : ℂ) (hu : u ≠ 1) (hv : v ≠ 1) (huv : 1 - u * conj v ≠ 0) :
    1 / (cayley u + conj (cayley v)) = (1 - u) * (1 - conj v) / 2 * (1 - u * conj v)⁻¹ := by
  rw [cayley_add_conj u v hu hv]
  have h1 : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h2 : (1 : ℂ) - conj v ≠ 0 := by
    rw [← map_one (starRingEnd ℂ), ← map_sub]
    exact (map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hv))
  field_simp

/-- The disc kernel `(1 − u v̄)⁻¹` has no pole on the open disc. -/
theorem one_sub_mul_conj_ne_zero (u v : ℂ) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    1 - u * conj v ≠ 0 := by
  intro h
  have h' : u * conj v = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖u * conj v‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖u‖ * ‖v‖ ≤ ‖u‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hu
  rw [h', norm_one] at hn
  exact lt_irrefl _ hn

/-- **The zeta pole, recentred at the critical line.** `ζ(1+q) − 1/q → γ` as `q → 0`: the
Dirichlet–Hardy kernel `ζ(1 + z + η̄)` is the half-plane Hardy kernel `1/(z + η̄)` plus a part
that stays bounded, tending to Euler's constant, at the boundary point `z + η̄ = 0`. -/
theorem tendsto_zeta_one_add_sub_inv :
    Tendsto (fun q : ℂ => riemannZeta (1 + q) - 1 / q) (𝓝[≠] 0)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hmap : Tendsto (fun q : ℂ => 1 + q) (𝓝[≠] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun q : ℂ => 1 + q) (𝓝 0) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simpa using hq
  refine (tendsto_riemannZeta_sub_one_div.comp hmap).congr (fun q => ?_)
  simp

end GppCayleyHardyKernel
