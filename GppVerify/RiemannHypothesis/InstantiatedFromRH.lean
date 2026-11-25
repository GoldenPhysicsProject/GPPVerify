/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import GppVerify.RiemannHypothesis.ZeroHilbertSpace
import GppVerify.RiemannHypothesis.UnitaryDilationWeights
import GppVerify.RiemannHypothesis.UnitaryHologramAssembly
import GppVerify.RiemannHypothesis.ZeroEigenvectorCorrespondence
import GppVerify.RiemannHypothesis.ArchimedeanCelestial

/-!
# The dictionary instantiated from `h : RiemannHypothesis`

Every statement here takes `h : RiemannHypothesis` (Mathlib's constant) as a hypothesis. Nothing
is imported from outside GPPVerify and no axiom is added; `h` is a variable of each theorem.

## What is instantiated
For `h : RiemannHypothesis`, every nontrivial zero `ρ` of `ζ` (strip, `ζ ρ = 0`) satisfies, at
once (`dictionary_of_rh`):

* `ρ.re = 1/2`, and `1 - ρ = conj ρ` (the shadow `Δ ↦ 1 - Δ` is complex conjugation at `ρ`);
* `ρ` is the conformal weight of an eigenstate of a unitary dilation (`IsWeight ρ`, the
  step-1 premise of `riemannHypothesis_of_isWeight`);
* the pole-shadow state `x^{ρ-1}` is orthogonal to every Beurling function `ρ_θ` on `(0,1]`;
* the state `x^{ρ-1}` is not normalizable on `(0,1]` (no bound state);
* the archimedean shadow coefficient has modulus one: `‖Γ_ℝ(1-ρ)/Γ_ℝ(ρ)‖ = 1`.

Globally: `NoBoundStates`, `ArithmeticReflectionPositivity`, `UnitaryRealization`, nonnegativity of
the Weil form on autocorrelations, and the zero Hilbert space of `ZeroHilbertSpace`.
-/

namespace GppInstantiated

open Complex Set MeasureTheory GppWeilCriterion GppArithmeticReflection GppBTSigmaSpectralTransform
  GppUnitaryWeights GppUnitaryHologram GppNymanBeurling GppZeroHilbert
open scoped ComplexConjugate

/-- `h : RiemannHypothesis` puts every nontrivial zero on the critical line (strip form). -/
theorem onLine (h : RiemannHypothesis) : OnLine := onLine_of_riemannHypothesis h

/-- Absence of bound states. -/
theorem noBoundStates (h : RiemannHypothesis) : NoBoundStates :=
  riemannHypothesis_iff_noBoundStates.1 h

/-- Arithmetic reflection positivity. -/
theorem arp (h : RiemannHypothesis) : ArithmeticReflectionPositivity :=
  arp_iff_rh_strip.2 (onLine h)

/-- The S-matrix unitarity realization of the zeta Gram form. -/
theorem unitaryRealization (h : RiemannHypothesis) : UnitaryRealization :=
  unitaryRealization_iff_arp.2 (arp h)

/-- Nonnegativity of the Weil form on autocorrelations of test functions. -/
theorem weilForm_nonneg (h : RiemannHypothesis) (f : Test) : 0 ≤ weilForm (autocorr f.1) :=
  weilForm_autocorr_nonneg (onLine h) f

/-- The zero Hilbert space, from `h`: a Hilbert space with a unitary dilation group, a state map
whose squared norm is the arithmetic Weil form, dilation = translation, and every nontrivial zero a
unimodular eigenvalue. -/
theorem zeroHilbertSpace (h : RiemannHypothesis) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (U : ℝ → (K ≃ₗᵢ[ℂ] K)) (O : Test → K),
      (∀ f, inner ℂ (O f) (O f) = (weilForm (autocorr f.1) : ℂ)) ∧
      (∀ x, U 0 x = x) ∧ (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ t f, U t (O f) = O ⟨shift t f.1, isTestFunction_shift t f.2⟩) ∧
      (∀ ρ : ℂ, ρ ∈ nontrivialZeros → ∃ v : K, v ≠ 0 ∧ ∀ t : ℝ,
        U t v = Complex.exp ((ρ - 1 / 2) * t) • v ∧ ‖Complex.exp ((ρ - 1 / 2) * t)‖ = 1) :=
  zero_hilbert_space (onLine h)

/-- **The dictionary at one zero.** -/
theorem dictionary_of_rh (h : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.re = 1 / 2 ∧ 1 - ρ = conj ρ ∧ IsWeight ρ ∧
      (∀ θ : ℝ, 0 < θ → θ ≤ 1 →
        ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling θ x = 0) ∧
      ¬ IsNormalizable ρ ∧ ‖GppArchimedeanCelestial.shadowCoeff ρ‖ = 1 := by
  have hre : ρ.re = 1 / 2 := onLine h ρ ⟨hz, h0, h1⟩
  refine ⟨hre, (one_sub_eq_conj_iff ρ).2 hre, isWeight_of_re hre,
    GppZeroEigenvector.zeta_eq_zero_iff_orthogonal h0 h1 |>.1 hz, ?_,
    GppArchimedeanCelestial.norm_shadowCoeff_of_re_half hre⟩
  rw [isNormalizable_iff, hre]; norm_num

/-- Every nontrivial zero is the weight of a unitary-dilation eigenstate, so the reduction
`riemannHypothesis_of_isWeight` closes: its premise holds. -/
theorem isWeight_of_zero (h : RiemannHypothesis) :
    ∀ ρ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → IsWeight ρ :=
  fun ρ hz hn h1 => isWeight_of_re (h ρ hz hn h1)

end GppInstantiated

#print axioms GppInstantiated.noBoundStates
#print axioms GppInstantiated.unitaryRealization
#print axioms GppInstantiated.dictionary_of_rh
#print axioms GppInstantiated.isWeight_of_zero
#print axioms GppInstantiated.zeroHilbertSpace
