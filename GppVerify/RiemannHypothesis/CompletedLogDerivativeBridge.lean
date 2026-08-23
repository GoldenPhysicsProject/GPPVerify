import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import GppVerify.RiemannHypothesis.GammaPlancherelDefect
import Mathlib.Tactic

/-!
# Completed logarithmic-derivative bridge: certified additive core

The earlier version of this file attempted to formalize several finite-product derivative
identities at once. Once this module was correctly wired into the root build, Lean exposed
proof-engineering failures in those candidate proofs. They are removed here rather than
hidden behind `sorry`.

The surviving core is the part actually needed for the global program:

* the positive-real Archimedean factor is nonzero;
* the finite prime response is the sum of the genuine local quantities
  `-zeta_p'/zeta_p`;
* on the critical line the finite `Wp` response is exactly twice the real part of that
  additive prime response.

The global prime logarithmic derivative is handled separately and more strongly by
`GlobalVonMangoldtBridge.lean`, using Mathlib's genuine von Mangoldt theorem for the
Riemann zeta function on `Re s > 1`.
-/

namespace GppCompletedLogDerivative

open Complex Real
open scoped BigOperators

/-- Positive-real Archimedean factor `pi^(-q/2) Gamma(q/2)`, written with `exp`. -/
noncomputable def realArchFactor (q : ℝ) : ℝ :=
  Real.exp (-(q / 2) * Real.log Real.pi) * Real.Gamma (q / 2)

/-- The Archimedean factor is nonzero on the positive real axis. -/
theorem realArchFactor_ne_zero {q : ℝ} (hq : 0 < q) : realArchFactor q ≠ 0 := by
  unfold realArchFactor
  apply mul_ne_zero (Real.exp_ne_zero _)
  apply Real.Gamma_ne_zero
  intro m hm
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Finite additive prime logarithmic derivative. Every summand is the genuine
`-zeta_p'/zeta_p`. -/
noncomputable def finitePrimeLogDerivative {ι : Type} [Fintype ι]
    (p : ι → ℝ) (s : ℂ) : ℂ :=
  ∑ i, GppCutkoskyWeil.minusLogDerivZetaP (p i) s

/-- Finite sum of the real prime response kernels. -/
noncomputable def finiteWp {ι : Type} [Fintype ι]
    (p : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, GppCutkoskyWeil.Wp (p i) t

/-- **Finite prime additive bridge on the critical line.** The real part of the finite
sum of genuine Euler logarithmic derivatives is exactly one half of the finite `Wp` sum. -/
theorem finiteWp_eq_two_mul_re_finitePrimeLogDerivative
    {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 1 < p i) (t : ℝ) :
    finiteWp p t =
      2 * (finitePrimeLogDerivative p (1 / 2 + t * Complex.I)).re := by
  classical
  unfold finiteWp finitePrimeLogDerivative
  calc
    (∑ i, GppCutkoskyWeil.Wp (p i) t)
        = ∑ i, 2 * (GppCutkoskyWeil.minusLogDerivZetaP
            (p i) (1 / 2 + t * Complex.I)).re := by
              apply Finset.sum_congr rfl
              intro i hi
              exact GppCutkoskyWeil.Wp_eq_two_mul_re_minusLogDerivZetaP (hp i) t
    _ = 2 * ∑ i, (GppCutkoskyWeil.minusLogDerivZetaP
            (p i) (1 / 2 + t * Complex.I)).re := by
              rw [Finset.mul_sum]
    _ = 2 * (∑ i, GppCutkoskyWeil.minusLogDerivZetaP
            (p i) (1 / 2 + t * Complex.I)).re := by
              rw [map_sum]

end GppCompletedLogDerivative

#print axioms GppCompletedLogDerivative.realArchFactor_ne_zero
#print axioms GppCompletedLogDerivative.finiteWp_eq_two_mul_re_finitePrimeLogDerivative
