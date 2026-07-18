import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The scaling generator has no globally square-integrable eigenfunction

## Golden Physics Project — ONON Framework Formalization
## Lean 4 / Mathlib v4.19.0

Source: `ONON5213.tex` (Zenodo record 21260806, "On the Nature of Nature: Celestial
Holography to the Zeta Zeros"), Theorem "Spectral–Weil Identification"
(`thm:spectral-weil`, ONON §… around the line defining `A = i·d/d\log|a|`) and
Theorem "No-ghost constraint on zeta zeros" (`thm:no-ghosts-onon`), which is the
final step of the paper's "Pathway 3 / Pathway 4" argument for the Riemann
Hypothesis via celestial-holographic unitarity and the Δ = 2s dictionary.

## What this file proves

`thm:no-ghosts-onon`, Step 1, asserts: "By the Spectral–Weil identification, the
ordinate `τ₀ = Im(ρ₀)` is an eigenvalue of the self-adjoint operator
`A = i·d/d\log|a|` on `ℋ`. The spectral projection `E_A({τ₀})` is therefore
non-zero." This is the step that turns "the Weil distribution has an atom at
`τ₀`" (a genuine, unconditional distributional fact, Theorem `thm:spectral-weil`
Step 4) into "`A` has a genuine, normalizable `L²` eigenvector at `τ₀`" (a
*point-spectrum* claim about the operator itself).

`A` acts on the non-compact factor `ℝ×₊` of `𝔸×/ℚ×` by `a ↦ e^t a`; after the
substitution `a = e^x` this is literally the generator `i·d/dx` acting on
`L²(ℝ, dx)` — the ordinary quantum-mechanical momentum operator. This file
proves, from first principles (no Mathlib gap, no external citation needed),
that **this operator has no point spectrum at all**: every formal solution of
the eigenvalue equation is either the zero function or fails to be globally
square-integrable. Consequently `E_A({t}) = 0` for *every* real `t`, for the
operator exactly as defined — directly contradicting the literal reading of
Step 1.

This is not a "gotcha" against celestial holography or against ONON — it is
the precise, checked reason *why* the paper's actual proof does not rest on
`E_A({τ₀}) ≠ 0` for the ordinary `L²` inner product at all, but on a
separately-introduced Cesàro-regularized inner product (`N_reg(σ)`, ONON
`thm:no-ghosts-onon` Step 4) under which `σ = 1/2` alone gives a finite,
positive norm. That regularization is a legitimate mathematical object — see
`GppSechIntegral.eigenstateNorm` in `EigenstateNormStrip.lean` for the closely
analogous (and rigorously convergent) Yakaboylu-side norm computation — but
its status as *the* canonical, uniquely-forced regularization, rather than one
convenient choice among many tuned to produce the critical line, is asserted
in ONON, not derived independently of the sought conclusion. That is exactly
the open gap already documented in `CauchyKernelPositive.lean` and
`WeilSupportLadder.lean`: this file pins down, for the *literal* un-regularized
operator, precisely why a further ingredient is unavoidable rather than a
one-line lemma.

## The mathematics

Write a formal eigenfunction `ψ = u + i·v : ℝ → ℂ` of `A = i·d/dx` at real
eigenvalue `t`, i.e. `ψ' = i·t·ψ`, in real and imaginary parts: this is
exactly the linear rotation system `u' = -t·v`, `v' = t·u`. We show:

1. `u² + v²` is constant on all of `ℝ` (`rotation_normSq_const`) — an
   elementary consequence of the product rule, with no exotic Mathlib
   dependency.
2. Since `volume : Measure ℝ` is not a finite measure (`Real.volume_univ`), a
   constant function is Lebesgue-integrable over all of `ℝ` only if it is the
   zero constant (`MeasureTheory.integrable_const_iff`).
3. Hence any solution with `u² + v² ∈ L¹(ℝ)` is identically zero
   (`no_nonzero_globally_L2_rotation_solution`): the operator has **no**
   nonzero eigenfunction in `L²(ℝ)`, at any real eigenvalue `t` whatsoever.
-/

namespace GppMomentumSpectrum

open MeasureTheory Set

/-- The Lebesgue measure on `ℝ` is not a finite measure: `volume univ = ∞`. -/
theorem not_isFiniteMeasure_volume_real : ¬ IsFiniteMeasure (volume : Measure ℝ) := by
  rw [not_isFiniteMeasure_iff]
  exact Real.volume_univ

/-- **Rotation-ODE norm-squared is constant.** If `(u, v) : ℝ → ℝ` solve the coupled
linear system `u' = -t·v`, `v' = t·u` — the real/imaginary-part form of the
eigenvalue equation `ψ' = i·t·ψ` for `ψ = u + i·v`, i.e. of `A ψ = t ψ` for the
momentum generator `A = i·d/dx` — then `u² + v²` is constant on all of `ℝ`. -/
theorem rotation_normSq_const {u v : ℝ → ℝ} {t : ℝ}
    (hu : ∀ x, HasDerivAt u (-t * v x) x) (hv : ∀ x, HasDerivAt v (t * u x) x)
    (x y : ℝ) : u x ^ 2 + v x ^ 2 = u y ^ 2 + v y ^ 2 := by
  have hderiv : ∀ z, HasDerivAt (fun w => u w * u w + v w * v w) 0 z := by
    intro z
    have h1 : HasDerivAt (fun w => u w * u w) (-t * v z * u z + u z * (-t * v z)) z :=
      (hu z).mul (hu z)
    have h2 : HasDerivAt (fun w => v w * v w) (t * u z * v z + v z * (t * u z)) z :=
      (hv z).mul (hv z)
    have hsum := h1.add h2
    have hval : -t * v z * u z + u z * (-t * v z) + (t * u z * v z + v z * (t * u z)) = 0 := by
      ring
    rwa [hval] at hsum
  have hdiff : Differentiable ℝ (fun w => u w * u w + v w * v w) :=
    fun z => (hderiv z).differentiableAt
  have hderiv' : ∀ z, deriv (fun w => u w * u w + v w * v w) z = 0 :=
    fun z => (hderiv z).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv' x y
  linear_combination hconst

/-- **No nonzero, globally square-integrable eigenfunction of the momentum
generator.** If `(u, v)` solves the rotation ODE at real eigenvalue `t` (i.e.
represents a formal eigenfunction `ψ = u + i·v` of `A = i·d/dx` with `A ψ = t
ψ`) and `u² + v²` is Lebesgue-integrable on all of `ℝ`, then `u` and `v`
vanish identically. Equivalently: for *every* real `t`, the only `L²(ℝ)`
solution of `A ψ = t ψ` is `ψ = 0` — the operator `A` has no point spectrum,
and `E_A({t}) = 0` for every `t`, contradicting the literal reading of
`thm:no-ghosts-onon` Step 1 (see the module docstring). -/
theorem no_nonzero_globally_L2_rotation_solution {u v : ℝ → ℝ} {t : ℝ}
    (hu : ∀ x, HasDerivAt u (-t * v x) x) (hv : ∀ x, HasDerivAt v (t * u x) x)
    (hint : Integrable (fun x => u x ^ 2 + v x ^ 2) (volume : Measure ℝ)) :
    ∀ x, u x = 0 ∧ v x = 0 := by
  have hconst : ∀ x, u x ^ 2 + v x ^ 2 = u 0 ^ 2 + v 0 ^ 2 :=
    fun x => rotation_normSq_const hu hv x 0
  have heq : (fun x => u x ^ 2 + v x ^ 2) = fun _ : ℝ => u 0 ^ 2 + v 0 ^ 2 := funext hconst
  rw [heq] at hint
  have hc0 : u 0 ^ 2 + v 0 ^ 2 = 0 := by
    rcases integrable_const_iff.mp hint with h0 | hfin
    · exact h0
    · exact absurd hfin not_isFiniteMeasure_volume_real
  intro x
  have hx0 : u x ^ 2 + v x ^ 2 = 0 := (hconst x).trans hc0
  have hune : (0:ℝ) ≤ u x ^ 2 := sq_nonneg _
  have hvne : (0:ℝ) ≤ v x ^ 2 := sq_nonneg _
  have hu2 : u x ^ 2 = 0 := le_antisymm (by linarith) hune
  have hv2 : v x ^ 2 = 0 := le_antisymm (by linarith) hvne
  exact ⟨sq_eq_zero_iff.mp hu2, sq_eq_zero_iff.mp hv2⟩

end GppMomentumSpectrum
