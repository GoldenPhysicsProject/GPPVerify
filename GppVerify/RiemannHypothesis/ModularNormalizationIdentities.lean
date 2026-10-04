import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exact modular normalization identities

Source: Codex, GPPDiscovery2 `research/2026-09-26_doubling_constants_modular_normalization.md`,
§§3–5 (the exact parts only).

* `kl_times_celestial`: with the celestial modular weight `P(λ) = πλ/sinh(πλ)` and the
  Kontorovich–Lebedev density `ρ(λ) = (2/π²) λ sinh(πλ)`, `ρ(λ) P(λ) = (2/π) λ²`; for `λ ≠ 0`,
  `P(λ) = (2/π) λ² / ρ(λ)` (the hyperbolic thermal factors cancel);
* `det_hermitian`: for the Hermitian matrix `X = x⁰ I + x⃗·σ⃗`, `det X = (x⁰)² − x₁² − x₂² − x₃²`;
* `eta_G_relation`: `η = c³/(4 G ħ)` is equivalent to `G = c³/(4 ħ η)` for `G, ħ, η, c ≠ 0`.

## Checks and scope

All three claims check. **Not formalized, and not claimed:** that these three normalization slots
correspond to `ħ`, `c`, `G` (the note labels this a conjectural dictionary and itself states that
no algebra fixes the SI values), the derivation of the endpoint entanglement density `η` (the note
observes that the naive `∫ λ²` is UV divergent), and the Bisognano–Wichmann reading of `P`.
`eta_G_relation` is a rearrangement of a stated relation, not a derivation of `G`. No RH claim.
-/

open Real

namespace GppModularNormalization

/-- Celestial modular spectral weight `P(λ) = πλ/sinh(πλ)`. -/
noncomputable def P (l : ℝ) : ℝ := Real.pi * l / Real.sinh (Real.pi * l)

/-- Kontorovich–Lebedev (causal-diamond) Plancherel density. -/
noncomputable def rhoKL (l : ℝ) : ℝ := 2 / Real.pi ^ 2 * l * Real.sinh (Real.pi * l)

/-- **`ρ_KL · P = (2/π) λ²`.** -/
theorem kl_times_celestial (l : ℝ) : rhoKL l * P l = 2 / Real.pi * l ^ 2 := by
  unfold rhoKL P
  by_cases hl : l = 0
  · simp [hl]
  · have hs : Real.sinh (Real.pi * l) ≠ 0 := by
      exact Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hl)
    have hp := Real.pi_ne_zero
    field_simp

/-- The thermal factors cancel: `P = (2/π) λ² / ρ_KL` for `λ ≠ 0`. -/
theorem celestial_eq_div (l : ℝ) (hl : l ≠ 0) : P l = 2 / Real.pi * l ^ 2 / rhoKL l := by
  have hs : Real.sinh (Real.pi * l) ≠ 0 := by
    exact Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hl)
  have hr : rhoKL l ≠ 0 := by
    unfold rhoKL
    have := Real.pi_ne_zero
    positivity
  rw [eq_div_iff hr, mul_comm]
  exact kl_times_celestial l

/-- **The Lorentzian norm of a Hermitian `2×2` matrix.** -/
theorem det_hermitian (x0 x1 x2 x3 : ℝ) :
    (!![(x0 + x3 : ℂ), (x1 : ℂ) + (x2 : ℂ) * Complex.I;
        (x1 : ℂ) - (x2 : ℂ) * Complex.I, (x0 - x3 : ℂ)]).det =
      ((x0 ^ 2 - x1 ^ 2 - x2 ^ 2 - x3 ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **`η = c³/(4Għ)` ⟺ `G = c³/(4ħη)`.** A rearrangement only. -/
theorem eta_G_relation (c G hbar eta : ℝ) (hc : c ≠ 0) (hG : G ≠ 0) (hh : hbar ≠ 0) (he : eta ≠ 0) :
    eta = c ^ 3 / (4 * G * hbar) ↔ G = c ^ 3 / (4 * hbar * eta) := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; rw [h]; field_simp

end GppModularNormalization
