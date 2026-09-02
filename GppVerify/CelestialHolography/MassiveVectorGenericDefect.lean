import GppVerify.CelestialHolography.MassiveCutPhysicalCoordinates
import Mathlib.Tactic

/-!
# Generic massive-vector state-sum defect algebra

The exact symbolic five-dimensional Yang--Mills audit found that the threshold
identity `C_V = 3 C_S` is not a generic cut identity. In rational kinematic
parameters `r,t`, its same-helicity defect is

  4 (r^2 - 1)^2 (1+t^2)^2 / (r^2+t^2)^2.

The exact generic sewing audit also gives the scalar and `D_s=4`
massive-vector-minus-scalar baselines. This module certifies the resulting
algebraic and positivity statements; it does not identify them with a full
Yang--Mills amplitude.
-/

namespace GppMassiveVectorGenericDefect

open GppMassiveCutPhysicalCoordinates

def sameHelicityDefect (r t : ℝ) : ℝ :=
  4 * (r ^ 2 - 1) ^ 2 * (1 + t ^ 2) ^ 2 / (r ^ 2 + t ^ 2) ^ 2

def sameHelicityScalarSewing (r t : ℝ) : ℝ :=
  4 * r ^ 4 * (1 + t ^ 2) ^ 2 /
    ((r ^ 2 + 1) ^ 2 * (r ^ 2 + t ^ 2) ^ 2)

def sameHelicityDs4Baseline (r t : ℝ) : ℝ :=
  4 * (r ^ 8 + 1) * (1 + t ^ 2) ^ 2 /
    ((r ^ 2 + 1) ^ 2 * (r ^ 2 + t ^ 2) ^ 2)

def mixedHelicityScalarPhysical (beta c u : ℝ) : ℝ :=
  u ^ 2 / (1 - beta * c) ^ 2

def mixedHelicityDs4Physical (beta c u : ℝ) : ℝ :=
  2 * (u ^ 2 - 8 * u + 8) / (1 - beta * c) ^ 2

def mixedHelicityVectorPhysical (beta c u : ℝ) : ℝ :=
  (3 * u ^ 2 - 16 * u + 16) / (1 - beta * c) ^ 2

theorem sameHelicityDefect_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDefect r t := by
  unfold sameHelicityDefect
  positivity

theorem sameHelicityScalarSewing_nonneg (r t : ℝ) :
    0 ≤ sameHelicityScalarSewing r t := by
  unfold sameHelicityScalarSewing
  positivity

theorem sameHelicityDs4Baseline_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDs4Baseline r t := by
  unfold sameHelicityDs4Baseline
  positivity

theorem mixedHelicityNumerator_ge_one
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 ≤ u ^ 2 - 8 * u + 8 := by
  have h7 : 0 ≤ 7 - u := by linarith
  have hprod : 0 ≤ (1 - u) * (7 - u) :=
    mul_nonneg (sub_nonneg.mpr hu1) h7
  nlinarith

theorem mixedHelicityScalarPhysical_nonneg (beta c u : ℝ) :
    0 ≤ mixedHelicityScalarPhysical beta c u := by
  unfold mixedHelicityScalarPhysical
  exact div_nonneg (sq_nonneg u) (sq_nonneg (1 - beta * c))

theorem mixedHelicityDs4Physical_nonneg
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ mixedHelicityDs4Physical beta c u := by
  unfold mixedHelicityDs4Physical
  have hn : 0 ≤ u ^ 2 - 8 * u + 8 :=
    le_trans zero_le_one (mixedHelicityNumerator_ge_one hu0 hu1)
  exact div_nonneg (mul_nonneg (by norm_num) hn) (sq_nonneg (1 - beta * c))

theorem mixedHelicityDs4Physical_pos
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hden : 1 - beta * c ≠ 0) :
    0 < mixedHelicityDs4Physical beta c u := by
  unfold mixedHelicityDs4Physical
  have hn : 0 < u ^ 2 - 8 * u + 8 :=
    lt_of_lt_of_le zero_lt_one (mixedHelicityNumerator_ge_one hu0 hu1)
  exact div_pos (mul_pos (by norm_num) hn) (sq_pos_of_ne_zero hden)

theorem mixedHelicityVectorNumerator_factor (u : ℝ) :
    3 * u ^ 2 - 16 * u + 16 = (3 * u - 4) * (u - 4) := by
  ring

theorem mixedHelicityVectorNumerator_ge_three
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    3 ≤ 3 * u ^ 2 - 16 * u + 16 := by
  have h10 : 0 ≤ 13 - 3 * u := by linarith
  have hprod : 0 ≤ (1 - u) * (13 - 3 * u) :=
    mul_nonneg (sub_nonneg.mpr hu1) h10
  nlinarith

theorem mixedHelicityVectorPhysical_nonneg
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ mixedHelicityVectorPhysical beta c u := by
  unfold mixedHelicityVectorPhysical
  have hn : 0 ≤ 3 * u ^ 2 - 16 * u + 16 :=
    le_trans (by norm_num) (mixedHelicityVectorNumerator_ge_three hu0 hu1)
  exact div_nonneg hn (sq_nonneg (1 - beta * c))

theorem mixedHelicityVectorPhysical_pos
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hden : 1 - beta * c ≠ 0) :
    0 < mixedHelicityVectorPhysical beta c u := by
  unfold mixedHelicityVectorPhysical
  have hn : 0 < 3 * u ^ 2 - 16 * u + 16 :=
    lt_of_lt_of_le (by norm_num) (mixedHelicityVectorNumerator_ge_three hu0 hu1)
  exact div_pos hn (sq_pos_of_ne_zero hden)

theorem mixedHelicityVector_eq_ds4_add_scalar (beta c u : ℝ) :
    mixedHelicityVectorPhysical beta c u =
      mixedHelicityDs4Physical beta c u + mixedHelicityScalarPhysical beta c u := by
  unfold mixedHelicityVectorPhysical mixedHelicityDs4Physical mixedHelicityScalarPhysical
  ring

@[simp] theorem sameHelicityDefect_one (t : ℝ) :
    sameHelicityDefect 1 t = 0 := by
  simp [sameHelicityDefect]

@[simp] theorem sameHelicityDefect_neg_one (t : ℝ) :
    sameHelicityDefect (-1) t = 0 := by
  simp [sameHelicityDefect]

theorem ds4Baseline_eq_two_scalar_add_defect
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDs4Baseline r t =
      2 * sameHelicityScalarSewing r t + sameHelicityDefect r t := by
  unfold sameHelicityDs4Baseline sameHelicityScalarSewing sameHelicityDefect
  have h1 : r ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg r]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have h2 : r ^ 2 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [h1, h2]
  ring

theorem sameHelicityDefect_le_ds4Baseline
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDefect r t ≤ sameHelicityDs4Baseline r t := by
  rw [ds4Baseline_eq_two_scalar_add_defect hr]
  have hs := sameHelicityScalarSewing_nonneg r t
  linarith

theorem sameHelicityScalarSewing_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityScalarSewing r t =
      rhoCoord r ^ 4 / (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  unfold sameHelicityScalarSewing rhoCoord betaCoord cosThetaCoord
  have hR : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have hT : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hRT : r ^ 2 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [hR, hT, hRT]
  ring

theorem sameHelicityDefect_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDefect r t =
      16 * betaCoord r ^ 2 /
        (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  unfold sameHelicityDefect betaCoord cosThetaCoord
  have hR : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have hT : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hRT : r ^ 2 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [hR, hT, hRT]
  ring

theorem sameHelicityDs4Baseline_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDs4Baseline r t =
      (2 * rhoCoord r ^ 4 + 16 * betaCoord r ^ 2) /
        (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  rw [ds4Baseline_eq_two_scalar_add_defect hr,
    sameHelicityScalarSewing_physical hr,
    sameHelicityDefect_physical hr]
  ring

@[simp] theorem sameHelicityDs4Baseline_one :
    sameHelicityDs4Baseline 1 1 = 2 := by
  norm_num [sameHelicityDs4Baseline]

theorem vector_ge_three_scalar_of_defect
    {Cv Cs r t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect r t) :
    3 * Cs ≤ Cv := by
  have h := sameHelicityDefect_nonneg r t
  linarith

theorem vector_eq_three_scalar_at_threshold
    {Cv Cs t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect 1 t) :
    Cv = 3 * Cs := by
  simpa using hdef

end GppMassiveVectorGenericDefect

#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_nonneg
#print axioms GppMassiveVectorGenericDefect.sameHelicityScalarSewing_nonneg
#print axioms GppMassiveVectorGenericDefect.sameHelicityDs4Baseline_nonneg
#print axioms GppMassiveVectorGenericDefect.mixedHelicityNumerator_ge_one
#print axioms GppMassiveVectorGenericDefect.mixedHelicityScalarPhysical_nonneg
#print axioms GppMassiveVectorGenericDefect.mixedHelicityDs4Physical_nonneg
#print axioms GppMassiveVectorGenericDefect.mixedHelicityDs4Physical_pos
#print axioms GppMassiveVectorGenericDefect.mixedHelicityVectorNumerator_factor
#print axioms GppMassiveVectorGenericDefect.mixedHelicityVectorNumerator_ge_three
#print axioms GppMassiveVectorGenericDefect.mixedHelicityVectorPhysical_nonneg
#print axioms GppMassiveVectorGenericDefect.mixedHelicityVectorPhysical_pos
#print axioms GppMassiveVectorGenericDefect.mixedHelicityVector_eq_ds4_add_scalar
#print axioms GppMassiveVectorGenericDefect.ds4Baseline_eq_two_scalar_add_defect
#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_le_ds4Baseline
#print axioms GppMassiveVectorGenericDefect.sameHelicityScalarSewing_physical
#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_physical
#print axioms GppMassiveVectorGenericDefect.sameHelicityDs4Baseline_physical
#print axioms GppMassiveVectorGenericDefect.vector_ge_three_scalar_of_defect
#print axioms GppMassiveVectorGenericDefect.vector_eq_three_scalar_at_threshold
