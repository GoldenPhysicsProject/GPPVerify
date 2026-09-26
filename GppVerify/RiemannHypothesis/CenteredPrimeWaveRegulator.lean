import GppVerify.RiemannHypothesis.VonMangoldtCosineBridge
import Mathlib.Tactic

/-!
# Centered half-density regulator for the global prime-wave response

Write the absolutely-convergent half-plane coordinate as

  a = 1/2 + eps.

Then `eps > 1/2` is exactly the condition `a > 1`.  In that honest region, the global
von-Mangoldt cosine bridge gives the damped arithmetic wave response around the half-density
center.  This file packages that coordinate change and records the sharp convergence barrier:
ordinary Dirichlet absolute convergence cannot reach `eps = 0`.

No analytic continuation, boundary-value theorem, or RH claim is made here.
-/

namespace GppCenteredPrimeWaveRegulator

open Complex
open ArithmeticFunction
open GppVonMangoldtCosine
open GppHaarPositivityWeil

/-- The centered radial coordinate measured from the half-density line. -/
noncomputable def centeredRadial (eps : ℝ) : ℝ := (1 : ℝ) / 2 + eps

/-- The centered damped prime-wave response. -/
noncomputable def centeredPrimeWave (eps t : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldt n *
    Real.exp (-Real.log n * centeredRadial eps) *
    Real.cos (Real.log n * t)

/-- `eps > 1/2` is exactly what puts the centered radial coordinate in the absolute-convergence
half-plane `a > 1`. -/
theorem one_lt_centeredRadial {eps : ℝ} (heps : (1 : ℝ) / 2 < eps) :
    1 < centeredRadial eps := by
  unfold centeredRadial
  linarith

/-- Exact global wave-particle identity in centered coordinates. -/
theorem centeredPrimeWave_eq_neg_zeta_logDeriv_re
    {eps t : ℝ} (heps : (1 : ℝ) / 2 < eps) :
    centeredPrimeWave eps t =
      (-(deriv riemannZeta
          (((centeredRadial eps : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta
          (((centeredRadial eps : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re := by
  rw [neg_zeta_logDeriv_re_eq_vonMangoldt_cosine_tsum
    (one_lt_centeredRadial heps)]
  rfl

/-- Every finite truncation of the centered damped prime-wave response is positive type,
for every real regulator.  This statement is algebraic and does not require convergence. -/
theorem finite_centeredPrimeWave_positiveType (eps : ℝ) (S : Finset ℕ) :
    PositiveType (fun t : ℝ =>
      ∑ n in S, vonMangoldt n *
        Real.exp (-Real.log n * centeredRadial eps) *
        Real.cos (Real.log n * t)) := by
  exact finite_vonMangoldt_cosine_positiveType (centeredRadial eps) S

/-- The principal half-density boundary `eps = 0` is strictly outside the region certified
by the elementary Dirichlet-series convergence condition `eps > 1/2`. -/
theorem principal_boundary_not_in_absolute_region :
    ¬ ((1 : ℝ) / 2 < 0) := by
  norm_num

end GppCenteredPrimeWaveRegulator

#print axioms GppCenteredPrimeWaveRegulator.one_lt_centeredRadial
#print axioms GppCenteredPrimeWaveRegulator.centeredPrimeWave_eq_neg_zeta_logDeriv_re
#print axioms GppCenteredPrimeWaveRegulator.finite_centeredPrimeWave_positiveType
