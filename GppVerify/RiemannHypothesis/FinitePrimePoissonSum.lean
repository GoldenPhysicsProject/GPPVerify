import GppVerify.RiemannHypothesis.PrimePoissonRadialBridge
import Mathlib.Tactic

/-!
# Finite-prime radial Poisson sum

The arbitrary-radial local Euler-factor identity promotes exactly to any finite
set of primes.  This is the finite bridge between the positive-type Poisson
kernels and a finite Euler logarithmic-derivative sum.  No infinite prime sum,
analytic continuation, explicit formula, or RH claim is made here.
-/

namespace GppFinitePrimePoisson

open Complex Real
open GppCutkoskyWeil GppPrimePoissonRadial

/-- Finite-prime Poisson response at radial parameter `a` and spectral parameter `t`. -/
noncomputable def finitePrimePoissonResponse (S : Finset ℕ) (a t : ℝ) : ℝ :=
  ∑ p in S, WpA (p : ℝ) a t

/-- Finite sum of local Euler-factor negative logarithmic derivatives. -/
noncomputable def finitePrimeLogDerivResponse (S : Finset ℕ) (a t : ℝ) : ℝ :=
  ∑ p in S, (minusLogDerivZetaP (p : ℝ) (a + t * Complex.I)).re

/-- **Exact finite-prime radial bridge.**  If every element of `S` is at least `2`,
then the finite Poisson response equals twice the real part of the corresponding
finite sum of local negative Euler logarithmic derivatives. -/
theorem finitePrimePoissonResponse_eq_two_mul_logDeriv
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    finitePrimePoissonResponse S a t =
      2 * finitePrimeLogDerivResponse S a t := by
  unfold finitePrimePoissonResponse finitePrimeLogDerivResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact WpA_eq_two_mul_re_minusLogDerivZetaP
    (by exact_mod_cast hS p hp) ha t

end GppFinitePrimePoisson

#print axioms GppFinitePrimePoisson.finitePrimePoissonResponse_eq_two_mul_logDeriv
