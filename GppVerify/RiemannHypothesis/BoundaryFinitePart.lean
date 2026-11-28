import GppVerify.RiemannHypothesis.KreinHPsi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Two-point boundary finite part for `Kpsi`

Status labels:

* `pole_kform_eq`: **PROVED**. The pole kernel is a cosh square minus a sinh
  square for every finite configuration.
* `pole_two_point`: **PROVED**. On `x = (0, a)`, `c = (1, -sech (a / 2))`,
  the pole finite part is `-A * tanh (a / 2) ^ 2` with
  `A = 2 * bigPsiI2 ^ 2`.
* `two_point_nonneg_iff`: **PROVED**. Two-point nonnegativity of `Kpsi` is
  equivalent to prime-carrying domination of that boundary square.
* `triG_eq_integral_triPsi_mul`: **PROVED**. `triG` is the autocorrelation
  integral of `triPsi`.
* `TwoPointPrimeDomination`: the prime-carrying domination hypothesis that `two_point_nonneg_iff` takes; arch-alone domination is false at two-point configurations, so the prime term is load-bearing already at the boundary.
  Turbo's D6-2 audit records arch-alone domination as false at two-point
  configurations, so the prime term is load-bearing already at the boundary.
-/

namespace GppBoundaryFinitePart

open GppKreinBridge GppKreinHPsi

noncomputable section

/-- The pole coefficient `A = 2 Ψ(i/2)²`. -/
def poleCoeff : ℝ := 2 * bigPsiI2 ^ 2

theorem poleCoeff_nonneg : 0 ≤ poleCoeff := by
  unfold poleCoeff bigPsiI2
  positivity

theorem triG_even (y : ℝ) : triG (-y) = triG y := by
  simp [triG, abs_neg]

theorem triG_eq_zero_of_abs_gt_two {y : ℝ} (hy : 2 < |y|) : triG y = 0 := by
  unfold triG
  rw [if_neg (by linarith : ¬ |y| ≤ 1), if_neg (by linarith : ¬ |y| ≤ 2)]

open MeasureTheory intervalIntegral

lemma triPsi_eq_zero_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : triPsi t = 0 := by
  unfold triPsi
  exact max_eq_left (by linarith)

lemma triPsi_eq_of_abs_le_one {t : ℝ} (h : |t| ≤ 1) : triPsi t = 1 - |t| := by
  unfold triPsi
  exact max_eq_right (by linarith)

lemma triPsi_continuous : Continuous triPsi := by
  unfold triPsi
  fun_prop

lemma integral_quad (a b c0 c1 c2 : ℝ) :
    ∫ t in a..b, (c0 + c1 * t + c2 * t ^ 2) =
      (c0 * b + c1 * b ^ 2 / 2 + c2 * b ^ 3 / 3) -
        (c0 * a + c1 * a ^ 2 / 2 + c2 * a ^ 3 / 3) := by
  have hi1 : IntervalIntegrable (fun t : ℝ => c0 + c1 * t) volume a b :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t : ℝ => c2 * t ^ 2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have hi3 : IntervalIntegrable (fun t : ℝ => c1 * t) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_add intervalIntegrable_const hi3,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp
  ring

lemma triG_eq_integral_triPsi_mul_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    triG y = ∫ t, triPsi t * triPsi (t - y) := by
  by_cases h2 : 2 < y
  · have hzero : ∀ t : ℝ, triPsi t * triPsi (t - y) = 0 := by
      intro t
      by_cases ht : 1 ≤ |t|
      · rw [triPsi_eq_zero_of_one_le_abs ht]
        simp
      · have ht1 : |t| < 1 := lt_of_not_ge ht
        have hle : 1 ≤ |t - y| := by
          have h : t - y < -1 := by
            have := abs_lt.mp ht1
            linarith
          rw [abs_of_neg (by linarith : t - y < 0)]
          linarith
        rw [triPsi_eq_zero_of_one_le_abs hle]
        simp
    rw [triG_eq_zero_of_abs_gt_two (by rw [abs_of_nonneg hy]; exact h2)]
    calc (0 : ℝ) = ∫ t, (0 : ℝ) := by simp
      _ = ∫ t, triPsi t * triPsi (t - y) :=
          integral_congr_ae (ae_of_all _ fun t => (hzero t).symm)
  · have hy2 : y ≤ 2 := by linarith
    have hcont : Continuous fun t : ℝ => triPsi t * triPsi (t - y) :=
      triPsi_continuous.mul
        (triPsi_continuous.comp (continuous_id.sub continuous_const))
    have hsupp : Function.support (fun t : ℝ => triPsi t * triPsi (t - y)) ⊆
        Set.Ioc (-2) 2 := by
      intro t ht
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ht
      have htlt : |t| < 1 := by
        by_contra h
        exact ht.1 (triPsi_eq_zero_of_one_le_abs (by linarith))
      have := abs_lt.mp htlt
      constructor <;> linarith
    have hint : (∫ t, triPsi t * triPsi (t - y)) =
        ∫ t in (-2)..2, triPsi t * triPsi (t - y) :=
      (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
    have hmid : (∫ t in (-2)..2, triPsi t * triPsi (t - y)) =
        ∫ t in (y - 1)..1, triPsi t * triPsi (t - y) := by
      have hsplit : (∫ t in (-2)..2, triPsi t * triPsi (t - y)) =
          (∫ t in (-2)..(y - 1), triPsi t * triPsi (t - y)) +
            (∫ t in (y - 1)..1, triPsi t * triPsi (t - y)) +
            (∫ t in (1)..2, triPsi t * triPsi (t - y)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable (-2) (y - 1)) (hcont.intervalIntegrable (y - 1) 2),
          ← intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable (y - 1) 1) (hcont.intervalIntegrable 1 2)]
        ring
      have hleft : (∫ t in (-2)..(y - 1), triPsi t * triPsi (t - y)) = 0 := by
        have h : (∫ t in (-2)..(y - 1), triPsi t * triPsi (t - y)) =
            ∫ _t in (-2)..(y - 1), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith : (-2 : ℝ) ≤ y - 1)] at ht
          obtain ⟨ht1, ht2⟩ := ht
          dsimp only
          have hle : 1 ≤ |t - y| := by
            rw [abs_of_nonpos (by linarith : t - y ≤ 0)]
            linarith [ht2]
          rw [triPsi_eq_zero_of_one_le_abs hle]
          simp
        rw [h]
        simp
      have hright : (∫ t in (1)..2, triPsi t * triPsi (t - y)) = 0 := by
        have h : (∫ t in (1)..2, triPsi t * triPsi (t - y)) =
            ∫ _t in (1)..2, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
          obtain ⟨ht1, ht2⟩ := ht
          dsimp only
          have hle : 1 ≤ |t| := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
            linarith [ht1]
          rw [triPsi_eq_zero_of_one_le_abs hle]
          simp
        rw [h]
        simp
      rw [hsplit, hleft, hright]
      simp
    rw [hint, hmid]
    by_cases h1 : y ≤ 1
    · have hsplit : (∫ t in (y - 1)..1, triPsi t * triPsi (t - y)) =
          (∫ t in (y - 1)..0, triPsi t * triPsi (t - y)) +
            (∫ t in (0)..y, triPsi t * triPsi (t - y)) +
            (∫ t in y..1, triPsi t * triPsi (t - y)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable (y - 1) 0) (hcont.intervalIntegrable 0 1),
          ← intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable 0 y) (hcont.intervalIntegrable y 1)]
        ring
      have hi1 : (∫ t in (y - 1)..0, triPsi t * triPsi (t - y)) =
          ∫ t in (y - 1)..0, ((1 - y) + (2 - y) * t + (1 : ℝ) * t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : y - 1 ≤ 0)] at ht
        obtain ⟨ht1, ht2⟩ := ht
        dsimp only
        have hpsi1 : triPsi t = 1 + t := by
          have hle : |t| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonpos ht2]
          ring
        have hpsi2 : triPsi (t - y) = 1 - y + t := by
          have hle : |t - y| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonpos (by linarith : t - y ≤ 0)]
          ring
        rw [hpsi1, hpsi2]
        ring
      have hi2 : (∫ t in (0)..y, triPsi t * triPsi (t - y)) =
          ∫ t in (0)..y, ((1 - y) + y * t + (-1 : ℝ) * t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hy] at ht
        obtain ⟨ht1, ht2⟩ := ht
        dsimp only
        have hpsi1 : triPsi t = 1 - t := by
          have hle : |t| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonneg ht1]
        have hpsi2 : triPsi (t - y) = 1 - y + t := by
          have hle : |t - y| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonpos (by linarith : t - y ≤ 0)]
          ring
        rw [hpsi1, hpsi2]
        ring
      have hi3 : (∫ t in y..1, triPsi t * triPsi (t - y)) =
          ∫ t in y..1, ((1 + y) + (-2 - y) * t + (1 : ℝ) * t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le h1] at ht
        obtain ⟨ht1, ht2⟩ := ht
        dsimp only
        have hpsi1 : triPsi t = 1 - t := by
          have hle : |t| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
        have hpsi2 : triPsi (t - y) = 1 + y - t := by
          have hle : |t - y| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - y)]
          ring
        rw [hpsi1, hpsi2]
        ring
      rw [hsplit, hi1, hi2, hi3, integral_quad, integral_quad, integral_quad]
      unfold triG
      rw [if_pos (by rw [abs_of_nonneg hy]; exact h1), abs_of_nonneg hy]
      ring
    · have h1le : 1 ≤ y := by linarith
      have hcalc : (∫ t in (y - 1)..1, triPsi t * triPsi (t - y)) =
          ∫ t in (y - 1)..1, ((1 - y) + y * t + (-1 : ℝ) * t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : y - 1 ≤ 1)] at ht
        obtain ⟨ht1, ht2⟩ := ht
        dsimp only
        have hpsi1 : triPsi t = 1 - t := by
          have hle : |t| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
        have hpsi2 : triPsi (t - y) = 1 - y + t := by
          have hle : |t - y| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht1, ht2]
          rw [triPsi_eq_of_abs_le_one hle, abs_of_nonpos (by linarith : t - y ≤ 0)]
          ring
        rw [hpsi1, hpsi2]
        ring
      rw [hcalc, integral_quad]
      unfold triG
      rw [if_neg (by rw [abs_of_nonneg hy]; linarith),
        if_pos (by rw [abs_of_nonneg hy]; exact hy2), abs_of_nonneg hy]
      ring

theorem triG_eq_integral_triPsi_mul (y : ℝ) :
    triG y = ∫ t, triPsi t * triPsi (t - y) := by
  have heven : ∀ z : ℝ,
      (∫ t, triPsi t * triPsi (t - -z)) = ∫ t, triPsi t * triPsi (t - z) := by
    intro z
    have hcontz : Continuous fun t : ℝ => triPsi (t - z) * triPsi t :=
      (triPsi_continuous.comp (continuous_id.sub continuous_const)).mul triPsi_continuous
    have h := integral_map_of_stronglyMeasurable
      (μ := volume) (φ := fun t : ℝ => t + z)
      (f := fun t : ℝ => triPsi (t - z) * triPsi t)
      (measurable_id.add_const z) hcontz.stronglyMeasurable
    rw [map_add_right_eq_self] at h
    simpa [mul_comm, sub_neg_eq_add] using h.symm
  by_cases hy : 0 ≤ y
  · exact triG_eq_integral_triPsi_mul_of_nonneg hy
  · have h := triG_eq_integral_triPsi_mul_of_nonneg (y := -y) (by linarith)
    rw [triG_even y] at h
    rw [heven y] at h
    exact h

theorem sq_sum_eq_sum_sum {n : ℕ} (c a : Fin n → ℝ) :
    (∑ i, c i * a i) ^ 2 = ∑ i, ∑ j, c i * c j * (a i * a j) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **PROVED**: the pole kernel is exactly a cosh square minus a sinh square. -/
theorem pole_kform_eq {n : ℕ} (x c : Fin n → ℝ) :
    kform poleTerm x c =
      poleCoeff *
        ((∑ i, c i * Real.cosh (x i / 2)) ^ 2 -
          (∑ i, c i * Real.sinh (x i / 2)) ^ 2) := by
  have hcosh : ∀ i j : Fin n,
      Real.cosh ((x i - x j) / 2) =
        Real.cosh (x i / 2) * Real.cosh (x j / 2) -
          Real.sinh (x i / 2) * Real.sinh (x j / 2) := by
    intro i j
    have h : (x i - x j) / 2 = x i / 2 - x j / 2 := by ring
    rw [h, Real.cosh_sub]
  have h1 := sq_sum_eq_sum_sum c (fun i => Real.cosh (x i / 2))
  have h2 := sq_sum_eq_sum_sum c (fun i => Real.sinh (x i / 2))
  have hexpand :
      kform poleTerm x c =
        poleCoeff *
          (∑ i, ∑ j,
            c i * c j *
              (Real.cosh (x i / 2) * Real.cosh (x j / 2) -
                Real.sinh (x i / 2) * Real.sinh (x j / 2))) := by
    rw [kform, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [poleTerm, poleCoeff, hcosh]
    ring
  rw [hexpand, h1, h2]
  congr 1
  simp [mul_sub, Finset.sum_sub_distrib]

/-- **PROVED**: on the cosh hyperplane, the pole channel is the negative sinh square. -/
theorem pole_kform_on_hyperplane {n : ℕ} (x c : Fin n → ℝ)
    (hker : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform poleTerm x c =
      -poleCoeff * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by
  rw [pole_kform_eq, hker]
  ring

/-- The two-point configuration `x = (0, a)`. -/
def twoX (a : ℝ) : Fin 2 → ℝ := ![0, a]

/-- The two-point coefficient vector on the cosh hyperplane. -/
def twoC (a : ℝ) : Fin 2 → ℝ := ![1, -(Real.cosh (a / 2))⁻¹]

theorem twoC_cosh_sum (a : ℝ) :
    ∑ i, twoC a i * Real.cosh (twoX a i / 2) = 0 := by
  have h : Real.cosh (a / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  simp [twoX, twoC, Fin.sum_univ_two, h]

theorem twoC_sinh_sum (a : ℝ) :
    ∑ i, twoC a i * Real.sinh (twoX a i / 2) = -Real.tanh (a / 2) := by
  have h : Real.cosh (a / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  simp [twoX, twoC, Fin.sum_univ_two, Real.tanh_eq_sinh_div_cosh]
  ring

/-- **PROVED**: the two-point pole finite part is `-A tanh²(a/2)`. -/
theorem pole_two_point (a : ℝ) :
    kform poleTerm (twoX a) (twoC a) =
      -poleCoeff * (Real.tanh (a / 2)) ^ 2 := by
  rw [pole_kform_on_hyperplane _ _ (twoC_cosh_sum a), twoC_sinh_sum]
  ring

theorem pole_two_point_nonpos (a : ℝ) :
    kform poleTerm (twoX a) (twoC a) ≤ 0 := by
  rw [pole_two_point]
  nlinarith [poleCoeff_nonneg, sq_nonneg (Real.tanh (a / 2))]

theorem kform_Kpsi {n : ℕ} (x c : Fin n → ℝ) :
    kform Kpsi x c =
      kform poleTerm x c - kform primeTerm x c + kform archTerm x c := by
  simp [kform, Kpsi, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub]

/-- **PROVED**: two-point nonnegativity of `Kpsi` is exactly prime-carrying
domination of the boundary square. -/
theorem two_point_nonneg_iff (a : ℝ) :
    0 ≤ kform Kpsi (twoX a) (twoC a) ↔
      poleCoeff * (Real.tanh (a / 2)) ^ 2 ≤
        kform archTerm (twoX a) (twoC a) - kform primeTerm (twoX a) (twoC a) := by
  rw [kform_Kpsi, pole_two_point]
  constructor <;> intro h <;> linarith

/-- **OPEN**: the remaining arithmetic hypothesis at two-point configurations. -/
def TwoPointPrimeDomination : Prop :=
  ∀ a : ℝ,
    poleCoeff * (Real.tanh (a / 2)) ^ 2 ≤
      kform archTerm (twoX a) (twoC a) - kform primeTerm (twoX a) (twoC a)

theorem two_point_nonneg_of_prime_domination
    (h : TwoPointPrimeDomination) (a : ℝ) :
    0 ≤ kform Kpsi (twoX a) (twoC a) :=
  (two_point_nonneg_iff a).2 (h a)

end

end GppBoundaryFinitePart

#print axioms GppBoundaryFinitePart.pole_kform_eq
#print axioms GppBoundaryFinitePart.pole_two_point
#print axioms GppBoundaryFinitePart.two_point_nonneg_iff

#print axioms GppBoundaryFinitePart.triG_eq_integral_triPsi_mul
