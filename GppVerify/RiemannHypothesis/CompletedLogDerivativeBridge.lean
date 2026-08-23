import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import GppVerify.RiemannHypothesis.GammaPlancherelDefect
import Mathlib.Tactic

/-!
# Completed logarithmic-derivative bridge

The finite local obstruction shows that neither finitely many Euler holonomies nor an
independent positive Archimedean channel can create a critical-strip zero.  The natural
next object is therefore the logarithmic derivative, where multiplicative local factors
become additive and the prime and Archimedean sectors can meet before a global limit is
taken.

This file establishes two exact finite-level ingredients.

* The real Archimedean factor

    `A(q) = exp (-(q/2) log pi) * Gamma(q/2)`

  has logarithmic derivative equal to the already-defined

    `g_infinity(q) = -log(pi)/2 + digamma(q/2)/2`.

* On the critical line, a finite sum of genuine Euler-factor logarithmic derivatives has
  real part exactly one half of the corresponding finite sum of the `Wp` kernels.

Thus the same additive completed-log-derivative language simultaneously contains the
Gamma/digamma term and the prime-power term.  No infinite Euler product, analytic
continuation, global explicit formula, or RH claim is asserted here.
-/

namespace GppCompletedLogDerivative

open Complex Real
open scoped BigOperators

/-- The positive-real Archimedean local factor `pi^(-q/2) Gamma(q/2)`, written with `exp`. -/
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

/-- **Actual derivative of the Archimedean factor.**  On `q > 0`, differentiating
`pi^(-q/2) Gamma(q/2)` gives `g_infinity(q)` times the factor itself. -/
theorem hasDerivAt_realArchFactor {q : ℝ} (hq : 0 < q) :
    HasDerivAt realArchFactor
      (GppGammaPlancherel.archimedeanG q * realArchFactor q) q := by
  have hq2 : 0 < q / 2 := by linarith
  have hpoles : ∀ m : ℕ, q / 2 ≠ -(m : ℝ) := by
    intro m hm
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hinner : HasDerivAt (fun x : ℝ => -(x / 2) * Real.log Real.pi)
      (-(1 / 2 : ℝ) * Real.log Real.pi) q := by
    convert ((hasDerivAt_id q).div_const 2).neg.mul_const (Real.log Real.pi) using 1 <;> ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(x / 2) * Real.log Real.pi))
      (Real.exp (-(q / 2) * Real.log Real.pi) *
        (-(1 / 2 : ℝ) * Real.log Real.pi)) q := hinner.exp
  have hGamma0 : HasDerivAt Real.Gamma (deriv Real.Gamma (q / 2)) (q / 2) :=
    (Real.differentiableAt_Gamma hpoles).hasDerivAt
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) q := by
    convert (hasDerivAt_id q).div_const 2 using 1 <;> ring
  have hGamma : HasDerivAt (fun x : ℝ => Real.Gamma (x / 2))
      (deriv Real.Gamma (q / 2) * (1 / 2 : ℝ)) q := hGamma0.comp q hhalf
  have hmul := hexp.mul hGamma
  unfold realArchFactor GppGammaPlancherel.archimedeanG GppDigamma.digamma
  convert hmul using 1
  · ring
  · have hGne : Real.Gamma (q / 2) ≠ 0 := Real.Gamma_ne_zero hpoles
    field_simp [hGne]
    ring

/-- Consequently the ordinary real logarithmic derivative of the Archimedean factor is
exactly the paper's `g_infinity(q)`. -/
theorem realArchFactor_logDeriv {q : ℝ} (hq : 0 < q) :
    deriv realArchFactor q / realArchFactor q = GppGammaPlancherel.archimedeanG q := by
  have hderiv := (hasDerivAt_realArchFactor hq).deriv
  rw [hderiv]
  field_simp [realArchFactor_ne_zero hq]

/-- Finite additive prime logarithmic derivative.  Every summand is the genuine
`-zeta_p'/zeta_p`, not a formal placeholder. -/
noncomputable def finitePrimeLogDerivative {ι : Type} [Fintype ι]
    (p : ι → ℝ) (s : ℂ) : ℂ :=
  ∑ i, GppCutkoskyWeil.minusLogDerivZetaP (p i) s

/-- Finite sum of the real `Wp` kernels attached to the same local factors. -/
noncomputable def finiteWp {ι : Type} [Fintype ι]
    (p : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, GppCutkoskyWeil.Wp (p i) t

/-- **Finite prime additive bridge on the critical line.**  The real part of the finite
sum of genuine local Euler logarithmic derivatives is exactly one half of the finite `Wp`
sum. -/
theorem finiteWp_eq_two_mul_re_finitePrimeLogDerivative
    {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 1 < p i) (t : ℝ) :
    finiteWp p t =
      2 * (finitePrimeLogDerivative p (1 / 2 + t * Complex.I)).re := by
  unfold finiteWp finitePrimeLogDerivative
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact GppCutkoskyWeil.Wp_eq_two_mul_re_minusLogDerivZetaP (hp i) t

/-- The conventionally signed finite prime term is therefore minus twice the real part of
the finite Euler logarithmic derivative. -/
theorem neg_finiteWp_eq_neg_two_mul_re_finitePrimeLogDerivative
    {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 1 < p i) (t : ℝ) :
    -finiteWp p t =
      -2 * (finitePrimeLogDerivative p (1 / 2 + t * Complex.I)).re := by
  rw [finiteWp_eq_two_mul_re_finitePrimeLogDerivative p hp t]
  ring

end GppCompletedLogDerivative

#print axioms GppCompletedLogDerivative.realArchFactor_ne_zero
#print axioms GppCompletedLogDerivative.hasDerivAt_realArchFactor
#print axioms GppCompletedLogDerivative.realArchFactor_logDeriv
#print axioms GppCompletedLogDerivative.finiteWp_eq_two_mul_re_finitePrimeLogDerivative
