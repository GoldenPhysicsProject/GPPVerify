/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Claude Code (workbench `claude-code/workbench`), 2026-11-13.

# (O2) restated: multiplicity-weighted, absolutely convergent, premise-isolated

`QuartetSpectral.O2` states (C1) as convergence of `Sfin x c (Z k)` along an
exhaustion. Two defects, recorded in the 2026-11-13 takeover report and adopted
by Turbo's ruling:

* **Multiplicity.** `Sfin` counts each zero once. The explicit formula counts
  zeros with multiplicity, and simplicity of the zeros of `ζ` is not proved.
* **Convergence.** Exhaustion-convergence does not supply the absolute
  convergence of the quartet-grouped sum (the terms are `O(|γ|⁻⁴)`).

Here the sum is a `HasSum` over the subtype `nontrivialZeros`, weighted by
`zeroMult ρ = analyticOrderNatAt riemannZeta ρ`. In `ℂ`, `HasSum` over an
arbitrary index type is unconditional, hence absolute (`O2mult_summable_norm`),
and independent of any exhaustion.

**In-tree input.** `GppExplicitFormulaAssembly.explicit_formula_zeroSum` already
proves the explicit formula with multiplicity and absolute convergence, for
`IsTestFunction f` = `C^∞` with compact support. `Fc x c` is a sum of triangles:
Lipschitz and compactly supported, but NOT `C^∞`. So the single analytic
obligation behind (O2) is the extension of that theorem from `C^∞` to the
piecewise-linear `Fc` (`EFFc` below; paper route: mollify `Fc` and pass to the
limit, with every term of the formula convergent and the zero sum dominated by
`|γ|⁻⁴`). Nothing in this file proves `EFFc`.

Labels: `O2mult` — OPEN (statement). `EFFc`, `FactorFc`, `WeilFormFc` — named
premises, stated with real content, not proved here. `O2mult_of_premises` and
`O2mult_summable_norm` — PROVED (pure assembly).
-/

import GppVerify.RiemannHypothesis.QuartetSpectral
import GppVerify.RiemannHypothesis.ExplicitFormulaAssembly

open ComplexConjugate

namespace GppQuartetO2

open GppQuartetSpectral GppKreinBridge GppKreinHPsi GppWeilCriterion GppXiZeroCounting
  GppMeyerSpectralWeil

/-- The summand of the spectral sum, weighted by the multiplicity of the zero:
`zeroMult ρ * (Fhat x c ρ * Fhat x c (1 - ρ))`. -/
noncomputable def term {n : ℕ} (x c : Fin n → ℝ) (ρ : ℂ) : ℂ :=
  (zeroMult ρ : ℂ) * (Fhat x c ρ * Fhat x c (1 - ρ))

/-- **(O2), restated** — OPEN. On `ker ℓ_c`, the multiplicity-weighted spectral
sum over all nontrivial zeros of `ζ` converges (unconditionally, hence
absolutely) to the defect form `kform Kpsi x c`. -/
def O2mult : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∑ i, c i * Real.cosh (x i / 2)) = 0 →
    HasSum (fun ρ : nontrivialZeros => term x c ρ) ((kform Kpsi x c : ℝ) : ℂ)

/-- Absolute convergence of the quartet-grouped sum, as a consequence of `O2mult`
(unconditional summability in `ℂ` is absolute summability). -/
theorem O2mult_summable_norm (h : O2mult) {n : ℕ} (x c : Fin n → ℝ)
    (hker : (∑ i, c i * Real.cosh (x i / 2)) = 0) :
    Summable (fun ρ : nontrivialZeros => ‖term x c ρ‖) :=
  summable_norm_iff.mpr (h n x c hker).summable

/-- **Premise (Guinand–Weil for `Fc`)** — OPEN, named. The in-tree explicit formula
`explicit_formula_zeroSum`, for the autocorrelation of `Fc x c` in place of a
`C^∞` test function: the zero sum with multiplicity converges and equals the Weil
form of the autocorrelation. -/
def EFFc : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ),
    HasSum (fun ρ : nontrivialZeros =>
        (zeroMult ρ : ℂ) *
          spectralTransform (GppArithmeticReflection.autocorr (Fc x c)) ρ)
      ((GppArithmeticReflection.weilForm (GppArithmeticReflection.autocorr (Fc x c)) : ℝ) : ℂ)

/-- **Premise (factorisation)** — named: the spectral transform of the
autocorrelation of `Fc` is the product `Fhat x c s * Fhat x c (1 - s)`. -/
def FactorFc : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ) (s : ℂ),
    spectralTransform (GppArithmeticReflection.autocorr (Fc x c)) s
      = Fhat x c s * Fhat x c (1 - s)

/-- **Premise (non-spectral identification)** — named: on `ker ℓ_c`, the Weil form
of the autocorrelation of `Fc` is the defect form `kform Kpsi x c`
(autocorrelation kernel `triG = tri ⋆ tri`, prime sum, pole term and the
archimedean identification). -/
def WeilFormFc : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∑ i, c i * Real.cosh (x i / 2)) = 0 →
    GppArithmeticReflection.weilForm (GppArithmeticReflection.autocorr (Fc x c))
      = kform Kpsi x c

/-- (PROVED, assembly) The three named premises give `O2mult`. -/
theorem O2mult_of_premises (hEF : EFFc) (hfac : FactorFc) (hW : WeilFormFc) : O2mult := by
  intro n x c hker
  have h := hEF n x c
  rw [hW n x c hker] at h
  have hf : (fun ρ : nontrivialZeros =>
        (zeroMult ρ : ℂ) *
          spectralTransform (GppArithmeticReflection.autocorr (Fc x c)) ρ)
      = fun ρ : nontrivialZeros => term x c ρ := by
    funext ρ
    unfold term
    rw [hfac n x c ρ]
  rw [hf] at h
  exact h

end GppQuartetO2
