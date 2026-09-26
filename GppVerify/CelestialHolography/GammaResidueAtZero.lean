import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

/-!
# Gamma simple-pole residue at zero

Mathlib defines `Gamma 0 = 0` by convention, so the mathematically meaningful
statement at the pole is a punctured-neighborhood limit.  Euler's recurrence

  Gamma(eps + 1) = eps * Gamma(eps)

turns the residue limit into ordinary continuity of Gamma at `1`.
-/

namespace GppGammaResidueAtZero

open Filter Set
open scoped Topology

/-- Real Gamma is continuous at `1`, as an immediate consequence of Mathlib's
real differentiability theorem away from the nonpositive integer poles. -/
theorem continuousAt_realGamma_one : ContinuousAt Real.Gamma 1 := by
  apply (Real.differentiableAt_Gamma ?_).continuousAt
  intro m h
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  linarith

/-- **Gamma residue at the origin.** In the punctured real neighborhood of zero,
`eps * Gamma(eps)` tends to `1`.  This is exactly the residue input used by the
raised-dimensional box factorization. -/
theorem tendsto_mul_realGamma_zero :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hadd0 : Tendsto (fun ε : ℝ => ε + 1) (nhds 0) (nhds 1) := by
    simpa using (tendsto_id.add tendsto_const_nhds :
      Tendsto (fun ε : ℝ => ε + 1) (nhds 0) (nhds (0 + 1)))
  have hadd : Tendsto (fun ε : ℝ => ε + 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hadd0.mono_left inf_le_left
  have hshift :
      Tendsto (fun ε : ℝ => Real.Gamma (ε + 1))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Function.comp_def] using continuousAt_realGamma_one.tendsto.comp hadd
  apply hshift.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := by simpa using hε
  exact Real.Gamma_add_one hε0

/-- The same Gamma residue holds on the physically relevant positive-regulator
neighborhood `ε → 0⁺`.  This removes a filter mismatch with the raised-box DCT,
whose one-channel majorant requires `0 ≤ ε`. -/
theorem tendsto_mul_realGamma_zero_pos :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε)
      (𝓝[>] 0) (nhds 1) := by
  apply tendsto_mul_realGamma_zero.mono_left
  apply nhdsWithin_mono
  intro ε hε
  simp only [mem_compl_iff, mem_singleton_iff]
  exact ne_of_gt hε

end GppGammaResidueAtZero

#print axioms GppGammaResidueAtZero.continuousAt_realGamma_one
#print axioms GppGammaResidueAtZero.tendsto_mul_realGamma_zero
#print axioms GppGammaResidueAtZero.tendsto_mul_realGamma_zero_pos
