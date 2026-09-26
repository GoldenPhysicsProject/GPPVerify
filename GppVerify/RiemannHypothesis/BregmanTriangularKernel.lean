import GppVerify.RiemannHypothesis.ZetaGibbsInformationGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Triangular integral kernels for one-parameter Gibbs Bregman divergences

If `A'=-U` and `U'=-g`, integration by parts gives the exact forward kernel

  D(beta || gamma) = ∫_beta^gamma (gamma-x) g(x) dx.

The reverse orientation follows by the same identity with the endpoints exchanged.
This file is analytic and abstract; the zeta Gibbs family is instantiated separately.
-/

namespace GppBregmanTriangularKernel

open Set MeasureTheory intervalIntegral
open GppZetaGibbsInformationGeometry

/-- Exact forward triangular Fisher kernel. -/
theorem bregmanKL_eq_triangular
    (A U g : ℝ → ℝ) (β γ : ℝ)
    (hA : ∀ x ∈ [[β, γ]], HasDerivAt A (-U x) x)
    (hU : ∀ x ∈ [[β, γ]], HasDerivAt U (-g x) x)
    (hg : ContinuousOn g [[β, γ]]) :
    bregmanKL A U β γ = ∫ x in β..γ, (γ - x) * g x := by
  have hUcont : ContinuousOn U [[β, γ]] := HasDerivAt.continuousOn hU
  have hnegUcont : ContinuousOn (fun x => -U x) [[β, γ]] := hUcont.neg
  have hnegUint : IntervalIntegrable (fun x => -U x) volume β γ :=
    hnegUcont.intervalIntegrable
  have hAint : (∫ x in β..γ, -U x) = A γ - A β :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hA hnegUint
  have hAeq : A γ - A β = -(∫ x in β..γ, U x) := by
    rw [← hAint]
    simp
  have hu : ∀ x ∈ [[β, γ]],
      HasDerivAt (fun y : ℝ => γ - y) (-1) x := by
    intro x hx
    simpa using (hasDerivAt_id x).const_sub γ
  have hv : ∀ x ∈ [[β, γ]],
      HasDerivAt (fun y : ℝ => -U y) (g x) x := by
    intro x hx
    convert (hU x hx).neg using 1 <;> simp
  have huInt : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume β γ :=
    intervalIntegrable_const
  have hgInt : IntervalIntegrable g volume β γ := hg.intervalIntegrable
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => γ - x) (u' := fun _ : ℝ => (-1 : ℝ))
    (v := fun x : ℝ => -U x) (v' := g)
    hu hv huInt hgInt
  have htri : (∫ x in β..γ, (γ - x) * g x) =
      (γ - β) * U β - ∫ x in β..γ, U x := by
    simpa [sub_eq_add_neg] using hibp
  unfold bregmanKL
  rw [hAeq, htri]
  ring

/-- The reverse orientation has the complementary triangular kernel. -/
theorem bregmanKL_reverse_eq_triangular
    (A U g : ℝ → ℝ) (β γ : ℝ)
    (hA : ∀ x ∈ [[β, γ]], HasDerivAt A (-U x) x)
    (hU : ∀ x ∈ [[β, γ]], HasDerivAt U (-g x) x)
    (hg : ContinuousOn g [[β, γ]]) :
    bregmanKL A U γ β = ∫ x in β..γ, (x - β) * g x := by
  have hforward := bregmanKL_eq_triangular A U g γ β
    (by simpa [uIcc_comm] using hA)
    (by simpa [uIcc_comm] using hU)
    (by simpa [uIcc_comm] using hg)
  rw [intervalIntegral.integral_symm] at hforward
  rw [hforward]
  apply intervalIntegral.integral_congr
  intro x hx
  ring

end GppBregmanTriangularKernel

#print axioms GppBregmanTriangularKernel.bregmanKL_eq_triangular
#print axioms GppBregmanTriangularKernel.bregmanKL_reverse_eq_triangular
