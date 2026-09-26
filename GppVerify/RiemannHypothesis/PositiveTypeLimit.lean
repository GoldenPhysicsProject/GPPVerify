import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.Tactic

/-!
# Positive type is closed under pointwise limits

This packages the finite-matrix limit argument already used internally in the
Poisson-kernel development. It is stated with complex-cast pointwise convergence,
which is exactly what is needed when a real kernel is represented by a convergent
complex Fourier/Dirichlet series.
-/

namespace GppPositiveTypeLimit

open Complex
open GppHaarPositivityWeil

/-- If every kernel in a sequence is positive type and its real values converge
pointwise after the canonical embedding into `ℂ`, then the limiting real kernel
is positive type. -/
theorem positiveType_of_tendsto
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ N, PositiveType (f N))
    (hlim : ∀ t : ℝ,
      Filter.Tendsto (fun N : ℕ => ((f N t : ℝ) : ℂ)) Filter.atTop
        (nhds ((g t : ℝ) : ℂ))) :
    PositiveType g := by
  intro M x c
  have hTendstoSum :
      Filter.Tendsto
        (fun N : ℕ => ∑ i : Fin M, ∑ j : Fin M,
          (starRingEnd ℂ) (c i) * c j * ((f N (x i - x j) : ℝ) : ℂ))
        Filter.atTop
        (nhds (∑ i : Fin M, ∑ j : Fin M,
          (starRingEnd ℂ) (c i) * c j * ((g (x i - x j) : ℝ) : ℂ))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    exact tendsto_const_nhds.mul (hlim (x i - x j))
  have hNonneg : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ (∑ i : Fin M, ∑ j : Fin M,
        (starRingEnd ℂ) (c i) * c j * ((f N (x i - x j) : ℝ) : ℂ)).re :=
    Filter.Eventually.of_forall (fun N => hf N M x c)
  exact ge_of_tendsto
    (Complex.continuous_re.continuousAt.tendsto.comp hTendstoSum) hNonneg

end GppPositiveTypeLimit

#print axioms GppPositiveTypeLimit.positiveType_of_tendsto
