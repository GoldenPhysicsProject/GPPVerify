import GppVerify.RiemannHypothesis.ZetaGibbsCriticalRegularization
import Mathlib.Tactic

/-!
# Differential algebra of a simple critical pole

If

  log Z(beta) = L(beta) - log(beta - 1),

then independently of any zeta-specific regularity theorem,

  (log Z)'  = L'  - 1/(beta-1),
  (log Z)'' = L'' + 1/(beta-1)^2.

This file formalizes the generic local calculus.  Applying it to
`L = log (regularizedPartition beta)` still requires the corresponding
zeta-specific differentiability/regularity input; no critical limit is assumed.
-/

namespace GppCriticalPoleDifferentialAlgebra

/-- A logarithmic coordinate with the universal simple-pole singularity split off. -/
noncomputable def criticalLog (L : ℝ → ℝ) (β : ℝ) : ℝ :=
  L β - Real.log (β - 1)

/-- Candidate first derivative after splitting the pole. -/
noncomputable def criticalLogPrime (Lp : ℝ → ℝ) (β : ℝ) : ℝ :=
  Lp β - 1 / (β - 1)

/-- Exact first-derivative decomposition. -/
theorem hasDerivAt_criticalLog
    {L : ℝ → ℝ} {β Lp : ℝ} (hβ : β ≠ 1)
    (hL : HasDerivAt L Lp β) :
    HasDerivAt (criticalLog L) (Lp - 1 / (β - 1)) β := by
  have hd : β - 1 ≠ 0 := sub_ne_zero.mpr hβ
  have hdist : HasDerivAt (fun x : ℝ => x - 1) 1 β := by
    simpa using (hasDerivAt_id β).sub_const 1
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (β - 1)) β := by
    convert hdist.log hd using 1 <;> field_simp [hd]
  simpa [criticalLog] using hL.sub hlog

/-- Exact second-derivative decomposition of the singular coordinate. -/
theorem hasDerivAt_criticalLogPrime
    {Lp : ℝ → ℝ} {β Lpp : ℝ} (hβ : β ≠ 1)
    (hLp : HasDerivAt Lp Lpp β) :
    HasDerivAt (criticalLogPrime Lp)
      (Lpp + 1 / (β - 1) ^ 2) β := by
  have hd : β - 1 ≠ 0 := sub_ne_zero.mpr hβ
  have hdist : HasDerivAt (fun x : ℝ => x - 1) 1 β := by
    simpa using (hasDerivAt_id β).sub_const 1
  have hinv := hdist.inv hd
  have hrecip : HasDerivAt (fun x : ℝ => 1 / (x - 1))
      (-1 / (β - 1) ^ 2) β := by
    convert hinv.const_mul 1 using 1 <;> field_simp [hd] <;> ring
  have h := hLp.sub hrecip
  convert h using 1 <;> simp [criticalLogPrime] <;> ring

/-- Algebraic consequence: once a regular second derivative `Lpp` is known,
the double-pole coefficient is exactly one. -/
theorem secondDerivative_split (Lpp β : ℝ) :
    Lpp + 1 / (β - 1) ^ 2 - Lpp = 1 / (β - 1) ^ 2 := by
  ring

end GppCriticalPoleDifferentialAlgebra

#print axioms GppCriticalPoleDifferentialAlgebra.hasDerivAt_criticalLog
#print axioms GppCriticalPoleDifferentialAlgebra.hasDerivAt_criticalLogPrime
#print axioms GppCriticalPoleDifferentialAlgebra.secondDerivative_split
