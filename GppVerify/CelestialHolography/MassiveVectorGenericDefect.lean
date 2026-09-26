import GppVerify.CelestialHolography.MassiveCutPhysicalCoordinates
import Mathlib.Tactic

/-!
# Generic massive-vector state-sum defect algebra

The exact symbolic five-dimensional Yang--Mills audit found that the threshold
identity `C_V = 3 C_S` is not a generic cut identity.  In the rational kinematic
parameters `r,t`, its same-helicity defect is

  4 (r^2 - 1)^2 (1+t^2)^2 / (r^2+t^2)^2.

A subsequent exact generic sewing audit evaluated the real-adjoint-scalar
contribution and the `D_s=4` massive-vector-minus-scalar baseline.  The latter
collapses to the unexpectedly simple numerator `r^8+1`:

  C4_same = 4 (r^8+1) (1+t^2)^2 /
    ((1+r^2)^2 (r^2+t^2)^2).

In physical coordinates `beta=|p|/E`, `rho=mu/E`, `c=cos(theta)`, these become

  Cs = rho^4/(1-beta*c)^2,
  Cv-3Cs = 16 beta^2/(1-beta*c)^2,
  C4 = (2 rho^4 + 16 beta^2)/(1-beta*c)^2.

For mixed helicity, writing `u = beta^2 sin(theta)^2`, the exact discovery
calculation gives

  Cs_mixed = u^2/(1-beta*c)^2,
  C4_mixed = 2 (u^2 - 8u + 8)/(1-beta*c)^2,
  Cv_mixed = (3u^2 - 16u + 16)/(1-beta*c)^2,

with the exact dimensional-reconstruction identity `Cv_mixed = C4_mixed + Cs_mixed`.
On physical kinematics `0 <= u <= 1`, both the `D_s=4` and massive-vector
numerators are uniformly positive.  This file certifies those algebraic and
positivity statements independently of the symbolic amplitude engine.
-/

namespace GppMassiveVectorGenericDefect

open GppMassiveCutPhysicalCoordinates

/-- Exact rational defect found by the generic symbolic state-sum audit. -/
def sameHelicityDefect (r t : ℝ) : ℝ :=
  4 * (r ^ 2 - 1) ^ 2 * (1 + t ^ 2) ^ 2 / (r ^ 2 + t ^ 2) ^ 2

/-- Exact same-helicity one-real-adjoint-scalar sewing from the generic audit. -/
def sameHelicityScalarSewing (r t : ℝ) : ℝ :=
  4 * r ^ 4 * (1 + t ^ 2) ^ 2 /
    ((r ^ 2 + 1) ^ 2 * (r ^ 2 + t ^ 2) ^ 2)

/-- Exact `D_s=4` same-helicity baseline obtained as massive-vector minus scalar. -/
def sameHelicityDs4Baseline (r t : ℝ) : ℝ :=
  4 * (r ^ 8 + 1) * (1 + t ^ 2) ^ 2 /
    ((r ^ 2 + 1) ^ 2 * (r ^ 2 + t ^ 2) ^ 2)

/-- Physical mixed-helicity scalar sewing in terms of
`u = beta^2 sin(theta)^2` and `c = cos(theta)`. -/
def mixedHelicityScalarPhysical (beta c u : ℝ) : ℝ :=
  u ^ 2 / (1 - beta * c) ^ 2

/-- Physical mixed-helicity `D_s=4` baseline. -/
def mixedHelicityDs4Physical (beta c u : ℝ) : ℝ :=
  2 * (u ^ 2 - 8 * u + 8) / (1 - beta * c) ^ 2

/-- Physical mixed-helicity massive-vector state sum from the exact audit. -/
def mixedHelicityVectorPhysical (beta c u : ℝ) : ℝ :=
  (3 * u ^ 2 - 16 * u + 16) / (1 - beta * c) ^ 2

/-- The generic correction is manifestly nonnegative. -/
theorem sameHelicityDefect_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDefect r t := by
  unfold sameHelicityDefect
  positivity

/-- The real-adjoint-scalar sewing is nonnegative everywhere in the rational chart. -/
theorem sameHelicityScalarSewing_nonneg (r t : ℝ) :
    0 ≤ sameHelicityScalarSewing r t := by
  unfold sameHelicityScalarSewing
  positivity

/-- The reconstructed `D_s=4` same-helicity baseline is nonnegative everywhere
in the rational chart. -/
theorem sameHelicityDs4Baseline_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDs4Baseline r t := by
  unfold sameHelicityDs4Baseline
  positivity

/-- On the physical interval `0 <= u <= 1`, the exact mixed-helicity polynomial
`u^2 - 8u + 8` is uniformly at least one. -/
theorem mixedHelicityNumerator_ge_one
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 ≤ u ^ 2 - 8 * u + 8 := by
  have h7 : 0 ≤ 7 - u := by linarith
  have hprod : 0 ≤ (1 - u) * (7 - u) :=
    mul_nonneg (sub_nonneg.mpr hu1) h7
  nlinarith

/-- The mixed scalar sewing is nonnegative for every real chart point. -/
theorem mixedHelicityScalarPhysical_nonneg (beta c u : ℝ) :
    0 ≤ mixedHelicityScalarPhysical beta c u := by
  unfold mixedHelicityScalarPhysical
  exact div_nonneg (sq_nonneg u) (sq_nonneg (1 - beta * c))

/-- Consequently the physical mixed-helicity `D_s=4` cut baseline is nonnegative
throughout `0 <= u <= 1`, even using Lean's totalized division convention. -/
theorem mixedHelicityDs4Physical_nonneg
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ mixedHelicityDs4Physical beta c u := by
  unfold mixedHelicityDs4Physical
  have hn : 0 ≤ u ^ 2 - 8 * u + 8 :=
    le_trans zero_le_one (mixedHelicityNumerator_ge_one hu0 hu1)
  exact div_nonneg (mul_nonneg (by norm_num) hn) (sq_nonneg (1 - beta * c))

/-- Away from the collinear denominator zero, the same physical mixed-helicity
baseline is strictly positive. -/
theorem mixedHelicityDs4Physical_pos
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hden : 1 - beta * c ≠ 0) :
    0 < mixedHelicityDs4Physical beta c u := by
  unfold mixedHelicityDs4Physical
  have hn : 0 < u ^ 2 - 8 * u + 8 :=
    lt_of_lt_of_le zero_lt_one (mixedHelicityNumerator_ge_one hu0 hu1)
  exact div_pos (mul_pos (by norm_num) hn) (sq_pos_of_ne_zero hden)

/-- The mixed massive-vector numerator has the exact factorization found by the
discovery audit. -/
theorem mixedHelicityVectorNumerator_factor (u : ℝ) :
    3 * u ^ 2 - 16 * u + 16 = (3 * u - 4) * (u - 4) := by
  ring

/-- On physical kinematics `0 <= u <= 1`, the mixed massive-vector numerator is
uniformly at least three. -/
theorem mixedHelicityVectorNumerator_ge_three
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    3 ≤ 3 * u ^ 2 - 16 * u + 16 := by
  have h10 : 0 ≤ 13 - 3 * u := by linarith
  have hprod : 0 ≤ (1 - u) * (13 - 3 * u) :=
    mul_nonneg (sub_nonneg.mpr hu1) h10
  nlinarith

/-- The massive-vector mixed-helicity cut is nonnegative on the physical interval. -/
theorem mixedHelicityVectorPhysical_nonneg
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ mixedHelicityVectorPhysical beta c u := by
  unfold mixedHelicityVectorPhysical
  have hn : 0 ≤ 3 * u ^ 2 - 16 * u + 16 :=
    le_trans (by norm_num) (mixedHelicityVectorNumerator_ge_three hu0 hu1)
  exact div_nonneg hn (sq_nonneg (1 - beta * c))

/-- Away from the collinear denominator zero, the massive-vector mixed-helicity
cut is strictly positive on `0 <= u <= 1`. -/
theorem mixedHelicityVectorPhysical_pos
    (beta c : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hden : 1 - beta * c ≠ 0) :
    0 < mixedHelicityVectorPhysical beta c u := by
  unfold mixedHelicityVectorPhysical
  have hn : 0 < 3 * u ^ 2 - 16 * u + 16 :=
    lt_of_lt_of_le (by norm_num) (mixedHelicityVectorNumerator_ge_three hu0 hu1)
  exact div_pos hn (sq_pos_of_ne_zero hden)

/-- **Mixed-helicity dimensional reconstruction.** The exact massive-vector sewing
is the `D_s=4` baseline plus one real-adjoint-scalar sewing. -/
theorem mixedHelicityVector_eq_ds4_add_scalar (beta c u : ℝ) :
    mixedHelicityVectorPhysical beta c u =
      mixedHelicityDs4Physical beta c u + mixedHelicityScalarPhysical beta c u := by
  unfold mixedHelicityVectorPhysical mixedHelicityDs4Physical mixedHelicityScalarPhysical
  ring

/-- The old `3:1` relation is recovered exactly on the threshold slice `r=1`. -/
@[simp] theorem sameHelicityDefect_one (t : ℝ) :
    sameHelicityDefect 1 t = 0 := by
  simp [sameHelicityDefect]

/-- The opposite threshold orientation `r=-1` has the same vanishing defect. -/
@[simp] theorem sameHelicityDefect_neg_one (t : ℝ) :
    sameHelicityDefect (-1) t = 0 := by
  simp [sameHelicityDefect]

/-- **Generic `D_s=4` closure.** Away from the degenerate `r=0` parametrization,
the exact massive-vector-minus-scalar baseline is two scalar sewings plus the
previously certified vector-minus-three-scalar defect. -/
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

/-- The positive defect is a rigorous lower bound for the reconstructed
same-helicity `D_s=4` baseline away from the degenerate `r=0` chart point. -/
theorem sameHelicityDefect_le_ds4Baseline
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDefect r t ≤ sameHelicityDs4Baseline r t := by
  rw [ds4Baseline_eq_two_scalar_add_defect hr]
  have hs := sameHelicityScalarSewing_nonneg r t
  linarith

/-- Exact chart-to-physical conversion of the scalar `mu^4` sewing. -/
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

/-- Exact physical form of the generic polarization defect. -/
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

/-- **Physical generic `D_s=4` numerator.** The baseline separates exactly into
a `mu^4` scalar term and a velocity/polarization term. -/
theorem sameHelicityDs4Baseline_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDs4Baseline r t =
      (2 * rhoCoord r ^ 4 + 16 * betaCoord r ^ 2) /
        (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  rw [ds4Baseline_eq_two_scalar_add_defect hr,
    sameHelicityScalarSewing_physical hr,
    sameHelicityDefect_physical hr]
  ring

/-- The exact generic baseline recovers the threshold state count `2`. -/
@[simp] theorem sameHelicityDs4Baseline_one :
    sameHelicityDs4Baseline 1 1 = 2 := by
  norm_num [sameHelicityDs4Baseline]

/-- If an explicit Yang--Mills sewing calculation identifies its vector/scalar
state-sum difference with the audited rational defect, then the vector sewing is
at least three scalar sewings.  The amplitude identification remains an explicit
input rather than being smuggled into the algebraic theorem. -/
theorem vector_ge_three_scalar_of_defect
    {Cv Cs r t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect r t) :
    3 * Cs ≤ Cv := by
  have h := sameHelicityDefect_nonneg r t
  linarith

/-- On the threshold slice, the same explicit identification reduces exactly to
`C_V = 3 C_S`. -/
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
