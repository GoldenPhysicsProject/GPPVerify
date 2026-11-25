import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The conformal group on the principal series of weight `Δ`

The one-dimensional conformal group `SL(2, ℝ)` acts on functions on the line through the weight-`Δ`
representation `(π_Δ(g) f)(x) = |cx + d|^{-2Δ} f((ax + b)/(cx + d))`.  This module defines the three
generating families on `ℝ → ℂ` and proves the group relations that make them an action of
`PSL(2, ℝ)`:

* translations `(T_b f)(x) = f(x + b)`;
* dilations `(D_a f)(x) = a^Δ f(a x)`, `a > 0`;
* the Weyl inversion `(W f)(x) = |x|^{-2Δ} f(-1/x)`.

For every weight `Δ ∈ ℂ` and `x` away from the singular points:

* `weyl_weyl`: `W² = 1`;
* `weyl_dil_weyl`: `W D_a W = D_{1/a}`;
* `dil_trans`: `D_a T_b = T_{b/a} D_a`;
* `weyl_trans_weyl`: `W T_b W` is the special conformal transformation
  `(K_b f)(x) = |1 - bx|^{-2Δ} f(x/(1 - bx))`;
* `modular_relation`: `(T_1 W)³ = 1`, the relation of the modular group `PSL(2, ℤ)` inside the
  conformal group.

These hold for all `Δ` because the cocycle `|·|^{-2Δ}` is multiplicative.  On the principal series
`Re Δ = 1/2` the generators are isometries of `L²(ℝ)`: `trans_isometry` and `dil_isometry`
preserve the norm, and `weyl_isometry_Ioi`, `weyl_isometry_Iio` show that `W` carries each
half-line isometrically onto the other.  The weight `Δ` is the conformal dimension of the primary;
on the half-line `W` is the shadow inversion `J` of `ConformalShadow` composed with the reflection
`x ↦ -x`.
-/

open Complex MeasureTheory Set

namespace GppConformalGroup

/-- `|y|^{-2Δ}` for a real `y`, as a complex number. -/
noncomputable def cocycle (Δ : ℂ) (y : ℝ) : ℂ := ((|y| : ℝ) : ℂ) ^ (-2 * Δ)

theorem cocycle_mul (Δ : ℂ) (y z : ℝ) : cocycle Δ (y * z) = cocycle Δ y * cocycle Δ z := by
  unfold cocycle
  rw [abs_mul, Complex.ofReal_mul, mul_cpow_ofReal_nonneg (abs_nonneg y) (abs_nonneg z)]

theorem cocycle_inv (Δ : ℂ) {y : ℝ} (hy : y ≠ 0) : cocycle Δ y⁻¹ * cocycle Δ y = 1 := by
  rw [← cocycle_mul, inv_mul_cancel₀ hy]
  unfold cocycle
  simp

theorem cocycle_ne_zero (Δ : ℂ) {y : ℝ} (hy : y ≠ 0) : cocycle Δ y ≠ 0 := by
  unfold cocycle
  have : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hy
  intro h
  rw [cpow_eq_zero_iff] at h
  exact this h.1

theorem cocycle_neg (Δ : ℂ) (y : ℝ) : cocycle Δ (-y) = cocycle Δ y := by
  unfold cocycle
  rw [abs_neg]

/-- Translation. -/
def trans (b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f (x + b)

/-- Dilation of weight `Δ`. -/
noncomputable def dilΔ (Δ : ℂ) (a : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ((a : ℝ) : ℂ) ^ Δ * f (a * x)

/-- The Weyl inversion of weight `Δ`. -/
noncomputable def weyl (Δ : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ := cocycle Δ x * f (-x⁻¹)

/-- `W² = 1`. -/
theorem weyl_weyl (Δ : ℂ) (f : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) : weyl Δ (weyl Δ f) x = f x := by
  unfold weyl
  have e : -(-x⁻¹)⁻¹ = x := by field_simp
  rw [e, cocycle_neg, ← mul_assoc, mul_comm (cocycle Δ x), cocycle_inv Δ hx, one_mul]

theorem inv_cpow_real (Δ : ℂ) {a : ℝ} (ha : 0 < a) :
    ((a⁻¹ : ℝ) : ℂ) ^ Δ = (((a : ℝ) : ℂ) ^ Δ)⁻¹ := by
  rw [Complex.ofReal_inv, inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm)]

theorem cocycle_pos (Δ : ℂ) {a : ℝ} (ha : 0 < a) : cocycle Δ a = ((a : ℝ) : ℂ) ^ (-2 * Δ) := by
  unfold cocycle
  rw [abs_of_pos ha]

/-- `W D_a W = D_{1/a}`. -/
theorem weyl_dil_weyl (Δ : ℂ) (f : ℝ → ℂ) {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    weyl Δ (dilΔ Δ a (weyl Δ f)) x = dilΔ Δ a⁻¹ f x := by
  unfold weyl dilΔ
  beta_reduce
  have ha0 : a ≠ 0 := ha.ne'
  have e : -(a * -x⁻¹)⁻¹ = a⁻¹ * x := by field_simp
  have e2 : a * -x⁻¹ = -(a * x⁻¹) := by ring
  rw [e2, cocycle_neg, cocycle_mul, cocycle_pos Δ ha] at *
  rw [show -(-(a * x⁻¹))⁻¹ = a⁻¹ * x by field_simp]
  have hc : cocycle Δ x * cocycle Δ x⁻¹ = 1 := by rw [mul_comm]; exact cocycle_inv Δ hx
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  have hp : ((a : ℝ) : ℂ) ^ Δ * ((a : ℝ) : ℂ) ^ (-2 * Δ) = ((a⁻¹ : ℝ) : ℂ) ^ Δ := by
    rw [← cpow_add _ _ ha', inv_cpow_real Δ ha, ← cpow_neg]
    congr 1
    ring
  linear_combination
    (((a : ℝ) : ℂ) ^ Δ * ((a : ℝ) : ℂ) ^ (-2 * Δ) * f (a⁻¹ * x)) * hc + f (a⁻¹ * x) * hp

/-- `D_a T_b = T_{b/a} D_a`. -/
theorem dil_trans (Δ : ℂ) (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (b x : ℝ) :
    dilΔ Δ a (trans b f) x = trans (b / a) (dilΔ Δ a f) x := by
  unfold dilΔ trans
  beta_reduce
  have : a * (x + b / a) = a * x + b := by field_simp
  rw [this]

/-- **The special conformal transformation.** `W T_b W f (x) = |1 - bx|^{-2Δ} f(x/(1 - bx))`. -/
theorem weyl_trans_weyl (Δ : ℂ) (f : ℝ → ℂ) {b x : ℝ} (hx : x ≠ 0) (hbx : b * x ≠ 1) :
    weyl Δ (trans b (weyl Δ f)) x = cocycle Δ (1 - b * x) * f (x / (1 - b * x)) := by
  unfold weyl trans
  beta_reduce
  have h1 : 1 - b * x ≠ 0 := fun h => hbx (by linarith)
  have e : -(-x⁻¹ + b)⁻¹ = x / (1 - b * x) := by
    have : -x⁻¹ + b = -(1 - b * x) / x := by field_simp; ring
    rw [this]
    field_simp
  have hc : cocycle Δ x * cocycle Δ (-x⁻¹ + b) = cocycle Δ (1 - b * x) := by
    rw [← cocycle_mul]
    have : x * (-x⁻¹ + b) = -(1 - b * x) := by field_simp; ring
    rw [this, cocycle_neg]
  rw [e, ← mul_assoc, hc]

/-- **The modular relation `(T_1 W)^3 = 1`.** The relation of `PSL(2, ℤ)` inside the conformal
group, for every weight `Δ`. -/
theorem modular_relation (Δ : ℂ) (f : ℝ → ℂ) {x : ℝ} (hx0 : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    trans 1 (weyl Δ (trans 1 (weyl Δ (trans 1 (weyl Δ f))))) x = f x := by
  unfold trans weyl
  beta_reduce
  have hy : -(x + 1)⁻¹ + 1 = x / (x + 1) := by field_simp; ring
  have hz : -(x / (x + 1))⁻¹ + 1 = -x⁻¹ := by field_simp; ring
  have hw : -(-x⁻¹)⁻¹ = x := by field_simp
  rw [hy, hz, hw]
  have hprod : cocycle Δ (x + 1) * (cocycle Δ (x / (x + 1)) * cocycle Δ (-x⁻¹)) = 1 := by
    rw [← cocycle_mul, ← cocycle_mul]
    have : (x + 1) * (x / (x + 1) * -x⁻¹) = -1 := by field_simp
    rw [this, cocycle_neg]
    unfold cocycle
    simp
  linear_combination (f x) * hprod

/-! ### Unitarity on the principal series `Re Δ = 1/2` -/

theorem norm_cocycle_half {Δ : ℂ} (h : Δ.re = 1 / 2) {y : ℝ} (hy : y ≠ 0) :
    ‖cocycle Δ y‖ = |y|⁻¹ := by
  unfold cocycle
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy)]
  have : (-2 * Δ).re = -1 := by simp [h]
  rw [this, Real.rpow_neg_one]

/-- Translations are isometries of `L²(ℝ)`. -/
theorem trans_isometry (b : ℝ) (f : ℝ → ℂ) :
    ∫ x, ‖trans b f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  unfold trans
  exact integral_add_right_eq_self (fun x => ‖f x‖ ^ 2) b

/-- Dilations of weight `Δ` with `Re Δ = 1/2` are isometries of `L²(ℝ)`. -/
theorem dil_isometry {Δ : ℂ} (h : Δ.re = 1 / 2) (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x, ‖dilΔ Δ a f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have e : ∀ x : ℝ, ‖dilΔ Δ a f x‖ ^ 2 = a * ‖f (a * x)‖ ^ 2 := by
    intro x
    unfold dilΔ
    rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos ha, h]
    have : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
    rw [this]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖f x‖ ^ 2) a,
    abs_of_pos (inv_pos.2 ha), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- The Weyl inversion carries the right half-line isometrically onto the left half-line. -/
theorem weyl_isometry_Ioi {Δ : ℂ} (h : Δ.re = 1 / 2) (f : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), ‖weyl Δ f x‖ ^ 2 = ∫ x in Iic (0 : ℝ), ‖f x‖ ^ 2 := by
  have hg := integral_comp_rpow_Ioi (fun y : ℝ => ‖f (-y)‖ ^ 2) (p := -1) (by norm_num)
  have hneg := integral_comp_neg_Ioi (0 : ℝ) (fun y : ℝ => ‖f y‖ ^ 2)
  rw [neg_zero] at hneg
  rw [hneg] at hg
  rw [← hg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  simp only [weyl, norm_mul, mul_pow, smul_eq_mul, abs_neg, abs_one, one_mul, Real.rpow_neg_one]
  rw [norm_cocycle_half h hx0.ne', abs_of_pos hx0, show (-1 : ℝ) - 1 = -2 by norm_num,
    Real.rpow_neg hx0.le, show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
  field_simp

/-- The Weyl inversion carries the left half-line isometrically onto the right half-line. -/
theorem weyl_isometry_Iio {Δ : ℂ} (h : Δ.re = 1 / 2) (f : ℝ → ℂ) :
    ∫ x in Iio (0 : ℝ), ‖weyl Δ f x‖ ^ 2 = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  have hg := integral_comp_rpow_Ioi (fun y : ℝ => ‖f y‖ ^ 2) (p := -1) (by norm_num)
  rw [← integral_Iic_eq_integral_Iio, ← neg_zero, ← integral_comp_neg_Ioi (0 : ℝ) (fun x => ‖weyl Δ f x‖ ^ 2), neg_zero, ← hg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  simp only [weyl, norm_mul, mul_pow, smul_eq_mul, abs_neg, abs_one, one_mul, Real.rpow_neg_one]
  rw [cocycle_neg, norm_cocycle_half h hx0.ne', abs_of_pos hx0, show (-1 : ℝ) - 1 = -2 by norm_num,
    Real.rpow_neg hx0.le, show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
  simp only [inv_neg, neg_neg]
  field_simp

end GppConformalGroup

#print axioms GppConformalGroup.weyl_weyl
#print axioms GppConformalGroup.weyl_dil_weyl
#print axioms GppConformalGroup.dil_trans
#print axioms GppConformalGroup.weyl_trans_weyl
#print axioms GppConformalGroup.modular_relation
#print axioms GppConformalGroup.trans_isometry
#print axioms GppConformalGroup.dil_isometry
#print axioms GppConformalGroup.weyl_isometry_Ioi
#print axioms GppConformalGroup.weyl_isometry_Iio
