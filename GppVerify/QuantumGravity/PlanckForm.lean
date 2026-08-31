import GppVerify.QuantumGravity.StefanBoltzmannFamily

/-!
# The Plancherel weight is a Planck oscillator partition function

From `Modular_Thermality_of_the_Celestial_Spectral_Weight.tex` (Theorem "Planck form, with
cancelling zero-point energy") and `Spectral_Weight_from_Principal_Series.tex` (same
theorem, stated identically) — the two papers Daniel has designated as the canonical
replacements for the loop/measure/block/blackbody paper series. Both state, for `λ > 0`
with `n_B(y) := (e^y-1)⁻¹` the Bose–Einstein occupation number:

```
P(λ) = 2πλ·[n_B(πλ) − n_B(2πλ)]
```

## What this file proves

`planck_form_bose_difference`: exactly the identity above, for every `λ ≠ 0` (the paper's
`λ > 0` hypothesis is not actually needed — the algebra is symmetric under `λ ↦ -λ` on both
sides, and only `λ ≠ 0` is needed to keep `sinh(πλ) ≠ 0` so `P` and `n_B(πλ)` are the
literal rational functions the definitions unfold to, not junk-value divisions by zero).

The proof is the paper's own one-line hyperbolic identity
`n_B(y) − n_B(2y) = 1/(2 sinh y)`, itself immediate from `e^{2y}-1 = (e^y-1)(e^y+1)` —
proved here as `nB_sub_nB_two_mul` and combined with `GppStefanBoltzmann.P`'s definition.

## What this file does NOT do

The paper's other two equivalent forms of the same identity (the oscillator-sum
`2πλ·Σ_{n≥0} e^{-2πλ(n+1/2)}` and the `E(x) = (x/2)coth(x/2)` zero-point-cancellation form)
are not separately formalized: Mathlib has no `coth` function at all, and the oscillator-sum
form is definitionally the same geometric series already packaged inside `Real.sinh`'s own
`exp`-based definition — restating it as an explicit `tsum` would be bookkeeping around the
same algebra proved once below, not new mathematical content. No axiom, no sorry.
-/

namespace GppPlanckForm

open Real GppStefanBoltzmann

/-- The Bose–Einstein occupation number `n_B(y) = 1/(e^y - 1)`. -/
noncomputable def nB (y : ℝ) : ℝ := 1 / (Real.exp y - 1)

/-- **The core hyperbolic identity**: `n_B(y) - n_B(2y) = 1/(2 sinh y)`, for every
`y ≠ 0`. Follows from `e^{2y} - 1 = (e^y-1)(e^y+1)` and `sinh y = (e^y - e^{-y})/2`. -/
theorem nB_sub_nB_two_mul {y : ℝ} (hy : y ≠ 0) :
    nB y - nB (2 * y) = 1 / (2 * Real.sinh y) := by
  set E : ℝ := Real.exp y with hE
  have hEpos : 0 < E := Real.exp_pos y
  have hE0 : E ≠ 0 := hEpos.ne'
  have hE1 : E ≠ 1 := by
    intro h
    exact hy (Real.exp_injective (by rw [← hE, h, Real.exp_zero]))
  have hEp1 : E + 1 ≠ 0 := by positivity
  have h2y : Real.exp (2 * y) = E * E := by
    rw [hE, show (2:ℝ) * y = y + y by ring, Real.exp_add]
  have hsinh : Real.sinh y = (E - E⁻¹) / 2 := by rw [Real.sinh_eq, hE, Real.exp_neg]
  have hden1 : E - 1 ≠ 0 := sub_ne_zero.mpr hE1
  have hden2 : E * E - 1 ≠ 0 := by
    intro h
    apply hEp1
    have hfact : (E - 1) * (E + 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hfact with h' | h'
    · exact absurd h' hden1
    · exact h'
  unfold nB
  rw [h2y, hsinh]
  field_simp
  -- Mathlib 4.33: `field_simp` leaves one `Real.exp y` unfolded next to the `E`s that
  -- `set` introduced, so `ring` sees two different atoms. Fold it back first.
  rw [← hE]
  -- Mathlib 4.33: the goal now carries `E ^ 2 - 1` while `hden2` states `E * E - 1`,
  -- so `field_simp` cannot see the denominator is nonzero. Same shape mismatch as in
  -- GrassmannianMass; restate the fact in the form the goal actually uses.
  have hden2' : E ^ 2 - 1 ≠ 0 := fun h => hden2 (by linear_combination h)
  field_simp
  ring

/-- **The Planck form of the Plancherel weight** (`Modular_Thermality`, Theorem "Planck
form"; `Spectral_Weight_from_Principal_Series`, same statement): for every `λ ≠ 0`,
`P(λ) = 2πλ·[n_B(πλ) − n_B(2πλ)]`. -/
theorem planck_form_bose_difference {lam : ℝ} (hlam : lam ≠ 0) :
    P lam = 2 * π * lam * (nB (π * lam) - nB (2 * π * lam)) := by
  have hpilam : π * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have key := nB_sub_nB_two_mul hpilam
  rw [show (2:ℝ) * π * lam = 2 * (π * lam) by ring, key]
  unfold GppStefanBoltzmann.P
  field_simp

end GppPlanckForm
