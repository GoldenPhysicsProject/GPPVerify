import Mathlib.Tactic

/-!
# Rational chart to physical massive-cut coordinates

The generic massive-vector discovery calculation uses rational parameters `r,t`.
This file isolates their exact conversion to the physical velocity/mass variables
and scattering angle:

  beta = (1-r^2)/(1+r^2),
  rho  = 2r/(1+r^2),
  cosTheta = (1-t^2)/(1+t^2),
  sinTheta = 2t/(1+t^2).

The identities below are pure kinematics.  They explain the repeated denominator
`1-beta*cosTheta` in the generic nonzero-mu Yang--Mills cut and certify the
physical range of `u = beta^2 sin(theta)^2` directly in the rational chart.
-/

namespace GppMassiveCutPhysicalCoordinates

noncomputable def betaCoord (r : ℝ) : ℝ := (1 - r ^ 2) / (1 + r ^ 2)
noncomputable def rhoCoord (r : ℝ) : ℝ := 2 * r / (1 + r ^ 2)
noncomputable def cosThetaCoord (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
noncomputable def sinThetaCoord (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)
noncomputable def mixedHelicityUCoord (r t : ℝ) : ℝ :=
  betaCoord r ^ 2 * sinThetaCoord t ^ 2

theorem beta_sq_add_rho_sq (r : ℝ) :
    betaCoord r ^ 2 + rhoCoord r ^ 2 = 1 := by
  unfold betaCoord rhoCoord
  have h : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  field_simp [h]
  ring

theorem cos_sq_add_sin_sq (t : ℝ) :
    cosThetaCoord t ^ 2 + sinThetaCoord t ^ 2 = 1 := by
  unfold cosThetaCoord sinThetaCoord
  have h : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [h]
  ring

theorem beta_sq_le_one (r : ℝ) : betaCoord r ^ 2 ≤ 1 := by
  have h := beta_sq_add_rho_sq r
  nlinarith [sq_nonneg (rhoCoord r)]

theorem sinTheta_sq_le_one (t : ℝ) : sinThetaCoord t ^ 2 ≤ 1 := by
  have h := cos_sq_add_sin_sq t
  nlinarith [sq_nonneg (cosThetaCoord t)]

theorem mixedHelicityUCoord_mem_unitInterval (r t : ℝ) :
    0 ≤ mixedHelicityUCoord r t ∧ mixedHelicityUCoord r t ≤ 1 := by
  constructor
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · unfold mixedHelicityUCoord
    have hb0 : 0 ≤ betaCoord r ^ 2 := sq_nonneg _
    have hs0 : 0 ≤ sinThetaCoord t ^ 2 := sq_nonneg _
    have hb1 : betaCoord r ^ 2 ≤ 1 := beta_sq_le_one r
    have hs1 : sinThetaCoord t ^ 2 ≤ 1 := sinTheta_sq_le_one t
    have hgap : 0 ≤ (betaCoord r ^ 2) * (1 - sinThetaCoord t ^ 2) :=
      mul_nonneg hb0 (sub_nonneg.mpr hs1)
    nlinarith

theorem one_sub_beta_mul_cosTheta (r t : ℝ) :
    1 - betaCoord r * cosThetaCoord t =
      2 * (r ^ 2 + t ^ 2) / ((1 + r ^ 2) * (1 + t ^ 2)) := by
  unfold betaCoord cosThetaCoord
  have hr : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have ht : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [hr, ht]
  ring

@[simp] theorem betaCoord_one : betaCoord 1 = 0 := by
  norm_num [betaCoord]

@[simp] theorem rhoCoord_one : rhoCoord 1 = 1 := by
  norm_num [rhoCoord]

end GppMassiveCutPhysicalCoordinates

#print axioms GppMassiveCutPhysicalCoordinates.beta_sq_add_rho_sq
#print axioms GppMassiveCutPhysicalCoordinates.cos_sq_add_sin_sq
#print axioms GppMassiveCutPhysicalCoordinates.mixedHelicityUCoord_mem_unitInterval
#print axioms GppMassiveCutPhysicalCoordinates.one_sub_beta_mul_cosTheta
