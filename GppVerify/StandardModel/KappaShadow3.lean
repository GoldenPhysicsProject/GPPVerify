import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# The shadow-3 sum rule and triality orbit for Yukawa curvatures

Source: kappa_paper.tex, "Fermion Mass Hierarchy from Division Algebra
Arithmetic" (Toupin 2026). The Yukawa curvature parameters
κ_s = 1 + 3cos²α_s (Fubini-Study sectional curvature on Gr(2,4)) satisfy
two exact facts independent of the fitted numerology in the paper:

1. The shadow-3 sum rule: for shadow-conjugate sectors with
   cos²α_s + cos²α_s̃ = 1, κ_s + κ_s̃ = 5 exactly, for *any* value of
   cos²α_s (Proposition "Shadow-3 sum rule").
2. The triality complementary-angle identity: the SM sector angles
   cos²α_d = 3/8, cos²α_u = 5/8 satisfy
   arccos(√(3/8)) + arccos(√(5/8)) = π/2 (used implicitly in Theorem
   "Triality orbit", establishing that the lepton angle π/4 is the
   arithmetic mean of the down/up angles).

The specific κ values (17/8, 5/2, 23/8) and their fitted agreement with
experimental Yukawa couplings (5-12% residuals, per the source) are
numerology, not exact mathematics, and are not formalized here.
-/

namespace GppKappaShadow3

/-- The Fubini-Study curvature formula κ(x) = 1 + 3x, as a function of
    x = cos²α rather than four separate numerical instances. -/
def kappaFS (x : ℝ) : ℝ := 1 + 3 * x

/-- **Shadow-3 sum rule**: for any x = cos²α, κ(x) + κ(1-x) = 5. Shadow-3
    conjugation sends cos²α ↦ 1 - cos²α, so this holds for every
    shadow-conjugate pair of sectors, not just the specific SM values. -/
theorem kappa_shadow3_sum_rule (x : ℝ) : kappaFS x + kappaFS (1 - x) = 5 := by
  unfold kappaFS; ring

theorem kappa_d_eq : kappaFS (3 / 8) = 17 / 8 := by unfold kappaFS; norm_num
theorem kappa_L_eq : kappaFS (1 / 2) = 5 / 2 := by unfold kappaFS; norm_num
theorem kappa_u_eq : kappaFS (5 / 8) = 23 / 8 := by unfold kappaFS; norm_num

/-- The SM instance of the sum rule: κ_u + κ_d = 5 exactly. -/
theorem kappa_ud_sum : kappaFS (3 / 8) + kappaFS (5 / 8) = 5 := by
  unfold kappaFS; norm_num

/-- **Triality complementary-angle identity**: arccos(√(3/8)) +
    arccos(√(5/8)) = π/2. Geometrically, this is why the lepton angle
    π/4 = (arccos(√(3/8)) + arccos(√(5/8)))/2 sits at the arithmetic
    mean of the down-type and up-type Yukawa angles. -/
theorem triality_complementary_angle :
    Real.arccos (Real.sqrt (3 / 8)) + Real.arccos (Real.sqrt (5 / 8)) = Real.pi / 2 := by
  have h38 : (0 : ℝ) ≤ 3 / 8 := by norm_num
  have h38' : (3 : ℝ) / 8 ≤ 1 := by norm_num
  have h58 : (0 : ℝ) ≤ 5 / 8 := by norm_num
  have h58' : (5 : ℝ) / 8 ≤ 1 := by norm_num
  set a := Real.arccos (Real.sqrt (3 / 8)) with ha_def
  set b := Real.arccos (Real.sqrt (5 / 8)) with hb_def
  have hsqrt38_nonneg : (0 : ℝ) ≤ Real.sqrt (3 / 8) := Real.sqrt_nonneg _
  have hsqrt58_nonneg : (0 : ℝ) ≤ Real.sqrt (5 / 8) := Real.sqrt_nonneg _
  have hsqrt38_le : Real.sqrt (3 / 8) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h38'
  have hsqrt58_le : Real.sqrt (5 / 8) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h58'
  have hcos_a : Real.cos a = Real.sqrt (3 / 8) :=
    Real.cos_arccos (by linarith) hsqrt38_le
  have hcos_b : Real.cos b = Real.sqrt (5 / 8) :=
    Real.cos_arccos (by linarith) hsqrt58_le
  have hsin_a : Real.sin a = Real.sqrt (5 / 8) := by
    rw [ha_def, Real.sin_arccos]
    rw [Real.sq_sqrt h38]
    norm_num
  have hsin_b : Real.sin b = Real.sqrt (3 / 8) := by
    rw [hb_def, Real.sin_arccos]
    rw [Real.sq_sqrt h58]
    norm_num
  have hcos_sum : Real.cos (a + b) = 0 := by
    rw [Real.cos_add, hcos_a, hcos_b, hsin_a, hsin_b]
    ring
  have ha_nonneg : 0 ≤ a := Real.arccos_nonneg _
  have hb_nonneg : 0 ≤ b := Real.arccos_nonneg _
  have ha_le : a ≤ Real.pi / 2 := by
    rw [ha_def, Real.arccos_eq_pi_div_two_sub_arcsin]
    have := Real.arcsin_nonneg.mpr hsqrt38_nonneg
    linarith
  have hb_le : b ≤ Real.pi / 2 := by
    rw [hb_def, Real.arccos_eq_pi_div_two_sub_arcsin]
    have := Real.arcsin_nonneg.mpr hsqrt58_nonneg
    linarith
  have hsum_mem : a + b ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith
  have hpi2_mem : (Real.pi / 2 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have : Real.cos (a + b) = Real.cos (Real.pi / 2) := by
    rw [hcos_sum, Real.cos_pi_div_two]
  exact Real.injOn_cos hsum_mem hpi2_mem this

end GppKappaShadow3
