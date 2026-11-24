import GppVerify.CelestialHolography.ConformalPrimaryWavefunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Klein–Gordon pairing (PSS File 2)

Pasterski–Shao, arXiv:1705.01027, eq. (3.6); Pasterski–Shao–Strominger, arXiv:1701.00049,
(A.1). This is File 2 of the PSS formalisation package
(GPP-bridge `MuseResearch/turbo-pss-inventory-spec-2026-11-13.md`, §3).

The paper's inner product on the Cauchy slice `X⁰ = t` of `ℝ^{1,d+1}` is

  `(Φ₁, Φ₂) = −i ∫ d^{d+1}x [ Φ₁ ∂₀ Φ₂* − ∂₀ Φ₁ Φ₂* ]`, `x` the spatial coordinates (3.6).

`kgPairing t Φ₁ Φ₂` is exactly this, on the fixed slice `X⁰ = t`, with `∂₀ Φ₂* = (∂₀ Φ₂)*`
(time derivative along a real line, then conjugate). The paper's remark that (3.6) is a positive
inner product on positive-energy wavefunctions (and its negative on negative-energy ones) is not
needed here.

## Main results

* `kgPairing_swap`: Hermitian symmetry, `(Φ₂, Φ₁) = conj (Φ₁, Φ₂)`. No hypotheses.
* `kgPairing_smul_left` and `kgPairing_smul_right`: `(cΦ, Ψ) = c(Φ, Ψ)` and
  `(Ψ, cΦ) = c̄(Ψ, Φ)`. No hypotheses.
* `kgPairing_add_left` and `kgPairing_add_right`: additivity, assuming differentiability in time
  on the slice and integrability of the two integrands.

## Named obligation (OPEN, not asserted)

* `KGPairingSliceIndependent d`: for smooth solutions of `□Φ = 0` whose Cauchy data on every slice
  have compact support, the pairing does not depend on the slice. This is the classical conservation
  law (differentiate in `t`, use `□ = −∂₀² + Δ`, integrate by parts). It is stated with its exact
  hypotheses, not proved, and not used. The conformal primaries of File 1 are not in this class:
  they are delta-normalisable, not compactly supported. The normalisability files use the
  fixed-slice pairing and say so.

No import from `GppVerify/RiemannHypothesis/`, directly or transitively (`scripts/check_pss_wall.py`).
-/

open Complex MeasureTheory
open scoped ContDiff

namespace GppKleinGordonPairing

open GppConformalPrimaryWavefunction

/-- The point of the slice `X⁰ = t` with spatial coordinates `x`. -/
def slicePoint {d : ℕ} (t : ℝ) (x : Fin (d + 1) → ℝ) : Spacetime d := Fin.cons t x

/-- The time derivative `∂₀ Φ` at the slice point `(t, x)`. -/
noncomputable def timeDeriv {d : ℕ} (Φ : Spacetime d → ℂ) (t : ℝ) (x : Fin (d + 1) → ℝ) : ℂ :=
  deriv (fun s : ℝ => Φ (slicePoint s x)) t

/-- The integrand of (3.6). -/
noncomputable def kgDensity {d : ℕ} (t : ℝ) (Φ₁ Φ₂ : Spacetime d → ℂ) (x : Fin (d + 1) → ℝ) : ℂ :=
  Φ₁ (slicePoint t x) * starRingEnd ℂ (timeDeriv Φ₂ t x)
    - timeDeriv Φ₁ t x * starRingEnd ℂ (Φ₂ (slicePoint t x))

/-- **The Klein–Gordon pairing on the slice `X⁰ = t`** (1705.01027 (3.6)). -/
noncomputable def kgPairing {d : ℕ} (t : ℝ) (Φ₁ Φ₂ : Spacetime d → ℂ) : ℂ :=
  -I * ∫ x, kgDensity t Φ₁ Φ₂ x

/-- **Hermitian symmetry.** `(Φ₂, Φ₁) = conj (Φ₁, Φ₂)`. -/
theorem kgPairing_swap {d : ℕ} (t : ℝ) (Φ₁ Φ₂ : Spacetime d → ℂ) :
    kgPairing t Φ₂ Φ₁ = starRingEnd ℂ (kgPairing t Φ₁ Φ₂) := by
  unfold kgPairing
  rw [map_mul, ← integral_conj]
  have h : ∀ x, kgDensity t Φ₂ Φ₁ x = -starRingEnd ℂ (kgDensity t Φ₁ Φ₂ x) := by
    intro x; unfold kgDensity; simp only [map_sub, map_mul, conj_conj]; ring
  simp_rw [h, integral_neg]
  simp [conj_I]

/-- The time derivative is linear under constant multiples. -/
theorem timeDeriv_smul {d : ℕ} (c : ℂ) (Φ : Spacetime d → ℂ) (t : ℝ) (x : Fin (d + 1) → ℝ) :
    timeDeriv (fun X => c * Φ X) t x = c * timeDeriv Φ t x := by
  unfold timeDeriv
  exact deriv_const_mul_field (v := fun s : ℝ => Φ (slicePoint s x)) c

/-- **Linearity in the first slot under scalars.** `(cΦ, Ψ) = c (Φ, Ψ)`. -/
theorem kgPairing_smul_left {d : ℕ} (t : ℝ) (c : ℂ) (Φ Ψ : Spacetime d → ℂ) :
    kgPairing t (fun X => c * Φ X) Ψ = c * kgPairing t Φ Ψ := by
  unfold kgPairing
  have h : ∀ x, kgDensity t (fun X => c * Φ X) Ψ x = c * kgDensity t Φ Ψ x := by
    intro x; unfold kgDensity; rw [timeDeriv_smul]; ring
  simp_rw [h, integral_const_mul]
  ring

/-- **Conjugate-linearity in the second slot under scalars.** `(Ψ, cΦ) = c̄ (Ψ, Φ)`. -/
theorem kgPairing_smul_right {d : ℕ} (t : ℝ) (c : ℂ) (Φ Ψ : Spacetime d → ℂ) :
    kgPairing t Ψ (fun X => c * Φ X) = starRingEnd ℂ c * kgPairing t Ψ Φ := by
  rw [kgPairing_swap, kgPairing_smul_left, map_mul, ← kgPairing_swap]

/-- The time derivative is additive for functions differentiable in time on the slice. -/
theorem timeDeriv_add {d : ℕ} {Φ Φ' : Spacetime d → ℂ} {t : ℝ} {x : Fin (d + 1) → ℝ}
    (h : DifferentiableAt ℝ (fun s : ℝ => Φ (slicePoint s x)) t)
    (h' : DifferentiableAt ℝ (fun s : ℝ => Φ' (slicePoint s x)) t) :
    timeDeriv (fun X => Φ X + Φ' X) t x = timeDeriv Φ t x + timeDeriv Φ' t x := by
  unfold timeDeriv
  exact deriv_add h h'

/-- **Additivity in the first slot.** Assumes differentiability in time on the slice and
integrability of both densities. -/
theorem kgPairing_add_left {d : ℕ} (t : ℝ) {Φ Φ' : Spacetime d → ℂ} (Ψ : Spacetime d → ℂ)
    (hd : ∀ x, DifferentiableAt ℝ (fun s : ℝ => Φ (slicePoint s x)) t)
    (hd' : ∀ x, DifferentiableAt ℝ (fun s : ℝ => Φ' (slicePoint s x)) t)
    (hi : Integrable (kgDensity t Φ Ψ)) (hi' : Integrable (kgDensity t Φ' Ψ)) :
    kgPairing t (fun X => Φ X + Φ' X) Ψ = kgPairing t Φ Ψ + kgPairing t Φ' Ψ := by
  unfold kgPairing
  have h : ∀ x, kgDensity t (fun X => Φ X + Φ' X) Ψ x = kgDensity t Φ Ψ x + kgDensity t Φ' Ψ x := by
    intro x; unfold kgDensity; rw [timeDeriv_add (hd x) (hd' x)]; ring
  simp_rw [h, integral_add hi hi']
  ring

/-- **Additivity in the second slot.** -/
theorem kgPairing_add_right {d : ℕ} (t : ℝ) (Ψ : Spacetime d → ℂ) {Φ Φ' : Spacetime d → ℂ}
    (hd : ∀ x, DifferentiableAt ℝ (fun s : ℝ => Φ (slicePoint s x)) t)
    (hd' : ∀ x, DifferentiableAt ℝ (fun s : ℝ => Φ' (slicePoint s x)) t)
    (hi : Integrable (kgDensity t Φ Ψ)) (hi' : Integrable (kgDensity t Φ' Ψ)) :
    kgPairing t Ψ (fun X => Φ X + Φ' X) = kgPairing t Ψ Φ + kgPairing t Ψ Φ' := by
  rw [kgPairing_swap, kgPairing_add_left t Ψ hd hd' hi hi', map_add, ← kgPairing_swap,
    ← kgPairing_swap]

/-- **Named obligation (OPEN, not asserted): slice independence.** For smooth solutions of the
massless Klein–Gordon equation whose Cauchy data have compact support on every slice, the pairing
(3.6) does not depend on the slice. Stated with its exact hypotheses; nothing in the tree uses
it. -/
def KGPairingSliceIndependent (d : ℕ) : Prop :=
  ∀ Φ₁ Φ₂ : Spacetime d → ℂ, ContDiff ℝ ∞ Φ₁ → ContDiff ℝ ∞ Φ₂ →
    (∀ X, box Φ₁ X = 0) → (∀ X, box Φ₂ X = 0) →
    (∀ t, HasCompactSupport (fun x : Fin (d + 1) → ℝ => Φ₁ (slicePoint t x))) →
    (∀ t, HasCompactSupport (fun x : Fin (d + 1) → ℝ => Φ₂ (slicePoint t x))) →
    ∀ t t' : ℝ, kgPairing t Φ₁ Φ₂ = kgPairing t' Φ₁ Φ₂

end GppKleinGordonPairing

#print axioms GppKleinGordonPairing.kgPairing_swap
#print axioms GppKleinGordonPairing.kgPairing_smul_left
#print axioms GppKleinGordonPairing.kgPairing_smul_right
#print axioms GppKleinGordonPairing.kgPairing_add_left
#print axioms GppKleinGordonPairing.kgPairing_add_right
