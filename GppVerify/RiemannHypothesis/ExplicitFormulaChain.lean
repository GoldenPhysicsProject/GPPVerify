/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import GppVerify.RiemannHypothesis.BTSigmaSpectralTransform
import GppVerify.RiemannHypothesis.AkgStatement
import GppVerify.RiemannHypothesis.ExplicitFormulaAssembly

/-!
# The explicit-formula chain in one statement

Weil's explicit formula connects the zeros of `ζ` to the primes, and the in-tree chain built on it
reaches the paired form of `WeilPositivityCriterion.lean` and the critical line. This file collects
the six links as one theorem, `explicit_formula_chain`, for test functions `f` that are smooth with
compact support in the log variable, with `ĝ(s) = ∫ g(u) e^{(s − 1/2) u} du` and
`weilForm g = pole g + archimedeanTerm g − Σ' Λ(n)/√n (g(log n) + g(−log n))`:

1. **Explicit formula** (`GppExplicitFormulaAssembly.explicit_formula_zeroSum`): the zero sum
   `Σ_ρ m(ρ) · ĝ(ρ)` over the nontrivial zeros, with `m(ρ) = zeroMult ρ` the order of vanishing,
   converges absolutely for `g = autocorr f = f ⋆ f̃` and equals `weilForm (autocorr f)`.
2. **Factorisation** (`GppGwefAssembly.gwef2_factorisation`): `ĝ_{f ⋆ f̃}(s) = f̂(s) · f̂(1 − s)`,
   which is the summand `conj(c(ι ρ)) · c(ρ)` of the paired form with `ι ρ = 1 − conj ρ`.
3. **Gram form** (`GppAKG.gram_zeta_eq`): the zeta Gram form of `f` is the real number
   `weilForm (autocorr f)`.
4. **Interpolation** (`GppGwefAssembly.gwef3_interpolation`, through `zetaTheory`): for every finite
   `ι`-closed, conjugation-symmetric set `S` of nontrivial zeros and every vector `v` on it,
   test functions bring the multiplicity-weighted Gram form within any `ε` of
   `pairedForm zetaInvolution S v`.
5. **Equivalence** (`GppBTSigmaSpectralTransform.arp_iff_rh_strip`): positivity of the Weil form on
   autocorrelations (`ArithmeticReflectionPositivity`) holds exactly when every nontrivial zero has
   `Re ρ = 1/2`.
6. **Mathlib's statement** (`GppBTSigmaSpectralTransform.riemannHypothesis_of_strip`): the strip
   form `∀ ρ ∈ nontrivialZeros, Re ρ = 1/2` gives `RiemannHypothesis`.
-/

open Complex
open GppMeyerSpectralWeil GppWeilCriterion GppKernelTheory GppXiZeroCounting GppShadowTheory

namespace GppExplicitFormulaChain

/-- **The explicit-formula chain.** Links 1 to 6 above, in one conjunction. -/
theorem explicit_formula_chain :
    -- 1. the explicit formula, zeros with multiplicity
    (∀ f : ℝ → ℝ, IsTestFunction f →
      Summable (fun ρ : nontrivialZeros =>
        (zeroMult ρ : ℂ) * spectralTransform (GppArithmeticReflection.autocorr f) ρ) ∧
      ∑' ρ : nontrivialZeros, (zeroMult ρ : ℂ) *
          spectralTransform (GppArithmeticReflection.autocorr f) ρ =
        (GppArithmeticReflection.weilForm (GppArithmeticReflection.autocorr f) : ℂ)) ∧
    -- 2. the factorisation of the autocorrelation transform
    (∀ f : ℝ → ℝ, IsTestFunction f → ∀ s : ℂ,
      spectralTransform (GppArithmeticReflection.autocorr f) s =
        spectralTransform f s * spectralTransform f (1 - s)) ∧
    -- 3. the zeta Gram form is the Weil form
    (∀ f : ZetaTest, shadowZeta.gram f =
      ((GppArithmeticReflection.weilForm (GppArithmeticReflection.autocorr f.1) : ℝ) : ℂ)) ∧
    -- 4. interpolation into the paired form
    (∀ S : Finset ℂ, (↑S : Set ℂ) ⊆ nontrivialZeros → (∀ ρ ∈ S, zetaInvolution ρ ∈ S) →
      ∀ v : ℂ → ℂ,
        (∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S ∧ v ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (v ρ)) →
        ∀ ε : ℝ, 0 < ε →
          ∃ f : ZetaTest, ‖zetaTheory.gram f - pairedForm zetaInvolution S v‖ < ε) ∧
    -- 5. positivity of the Weil form is the critical-line statement
    (GppArithmeticReflection.ArithmeticReflectionPositivity ↔
      ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) ∧
    -- 6. the strip form gives Mathlib's statement
    ((∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) → RiemannHypothesis) :=
  ⟨fun f hf => GppExplicitFormulaAssembly.explicit_formula_zeroSum hf,
   fun f hf s => GppGwefAssembly.gwef2_factorisation hf s,
   GppAKG.gram_zeta_eq,
   fun S hS hSι v hv ε hε => zetaTheory.interpolation S hS hSι v hv ε hε,
   GppBTSigmaSpectralTransform.arp_iff_rh_strip,
   GppBTSigmaSpectralTransform.riemannHypothesis_of_strip⟩

end GppExplicitFormulaChain

#print axioms GppExplicitFormulaChain.explicit_formula_chain
