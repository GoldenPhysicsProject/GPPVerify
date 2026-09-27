import GppVerify.RiemannHypothesis.NumberGibbsQuadraticConfinement
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Pointwise parameter derivatives for the quadratically confined number-Gibbs family

The uniform quadratic-confinement estimates already provide common summable
log-moment envelopes on compact parameter regions.  This file isolates the
other ingredient needed for termwise differentiation: the exact first and
second derivatives of each Gibbs summand with respect to the two parameters.
-/

namespace GppNumberGibbsQuadraticTermDerivatives

open GppNumberGibbsTwoParameterStrict

/-- Differentiating one number-Gibbs summand in the inverse-temperature
parameter contributes one factor `-log(n+1)`. -/
theorem numberGibbsWeight_hasDerivAt_beta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun b : ℝ => numberGibbsWeight b η n)
      (numberGibbsWeight β η n * (-numberLogEnergy n)) β := by
  let L : ℝ := numberLogEnergy n
  have hinner : HasDerivAt
      (fun b : ℝ => -b * L - η * L ^ 2) (-L) β := by
    convert ((hasDerivAt_id β).neg.mul_const L).sub_const (η * L ^ 2) using 1 <;> ring
  have h := (Real.hasDerivAt_exp (-β * L - η * L ^ 2)).comp β hinner
  simpa [numberGibbsWeight, numberLogEnergy, L] using h

/-- Differentiating one number-Gibbs summand in the quadratic-confinement
parameter contributes one factor `-(log(n+1))^2`. -/
theorem numberGibbsWeight_hasDerivAt_eta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun e : ℝ => numberGibbsWeight β e n)
      (numberGibbsWeight β η n * (-(numberLogEnergy n) ^ 2)) η := by
  let L : ℝ := numberLogEnergy n
  have hinner : HasDerivAt
      (fun e : ℝ => -β * L - e * L ^ 2) (-(L ^ 2)) η := by
    convert (hasDerivAt_const η (-β * L)).sub
      ((hasDerivAt_id η).mul_const (L ^ 2)) using 1 <;> ring
  have h := (Real.hasDerivAt_exp (-β * L - η * L ^ 2)).comp η hinner
  simpa [numberGibbsWeight, numberLogEnergy, L] using h

/-- The second `β` derivative of one Gibbs summand contributes the positive
square of the log-energy.  This is the termwise `ββ` Hessian entry. -/
theorem numberGibbsWeight_beta_deriv_hasDerivAt_beta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun b : ℝ => numberGibbsWeight b η n * (-numberLogEnergy n))
      (numberGibbsWeight β η n * numberLogEnergy n ^ 2) β := by
  have h := (numberGibbsWeight_hasDerivAt_beta β η n).mul_const (-numberLogEnergy n)
  convert h using 1 <;> ring

/-- The mixed `η` derivative of the `β` derivative contributes the cube of the
log-energy.  Equality of the opposite mixed order is immediate from the same
closed-form summand and can be promoted after countable differentiation. -/
theorem numberGibbsWeight_beta_deriv_hasDerivAt_eta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun e : ℝ => numberGibbsWeight β e n * (-numberLogEnergy n))
      (numberGibbsWeight β η n * numberLogEnergy n ^ 3) η := by
  have h := (numberGibbsWeight_hasDerivAt_eta β η n).mul_const (-numberLogEnergy n)
  convert h using 1 <;> ring

/-- The second `η` derivative of one Gibbs summand contributes the fourth power
of the log-energy.  This is the termwise `ηη` Hessian entry. -/
theorem numberGibbsWeight_eta_deriv_hasDerivAt_eta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun e : ℝ => numberGibbsWeight β e n * (-(numberLogEnergy n) ^ 2))
      (numberGibbsWeight β η n * numberLogEnergy n ^ 4) η := by
  have h := (numberGibbsWeight_hasDerivAt_eta β η n).mul_const (-(numberLogEnergy n) ^ 2)
  convert h using 1 <;> ring

end GppNumberGibbsQuadraticTermDerivatives

#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_hasDerivAt_beta
#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_hasDerivAt_eta
#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_beta_deriv_hasDerivAt_beta
#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_beta_deriv_hasDerivAt_eta
#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_eta_deriv_hasDerivAt_eta
