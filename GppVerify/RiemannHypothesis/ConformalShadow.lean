import GppVerify.RiemannHypothesis.ArchimedeanCelestial
import GppVerify.RiemannHypothesis.NymanBeurlingBoundStates

/-!
# The 1D celestial CFT: dilation, shadow inversion, primary states

The kinematics of the one-dimensional celestial conformal quantum mechanics on `L²((0,∞), dx)`.

* the dilation group `(D_a f)(x) = √a f(a x)`;
* the **shadow inversion** `(J f)(x) = x⁻¹ f(x⁻¹)`;
* the primary states `x^{ρ-1}` of conformal weight `ρ`.

The group relations are exact: `J² = 1` (`shadow_shadow`), `J D_a J = D_{1/a}` (`shadow_dil`),
and both `D_a` and `J` preserve `∫_0^∞ |f|²` (`integral_norm_sq_dil`, `integral_norm_sq_shadow`).
`J` exchanges the weight `ρ` with its shadow `1 - ρ`: `J x^{ρ-1} = x^{(1-ρ)-1}` (`shadow_cpow`)
and swaps the halves `(0,1]` and `[1,∞)`, carrying `L²(0,1]` isometrically onto `L²[1,∞)`
(`shadow_eq_zero_of_lt_one`, `integral_norm_sq_shadow_Ioi`).  In the Mellin picture `J`
is the shadow transform: `mellin (J f) s = mellin f (1 - s)` (`mellin_shadow`).

The two states that carry the theory:

* the Gaussian `g(x) = e^{-π x²}` (archimedean ground state): `mellin (J g) s = shadowCoeff s ·
  mellin g s` on the strip (`mellin_shadow_gaussian`), the shadow coefficient `Γ_ℝ(1-s)/Γ_ℝ(s)`;
* the arithmetic profile `χ(x) = {1/x}` whose Mellin transform is `-ζ(s)/s`: its shadow obeys
  `(1-s) · shadowCoeff s · mellin (J χ) s = s · mellin χ s` (`shadow_arith_identity`), the
  arithmetic side of the same relation.
-/

open Complex MeasureTheory Set

namespace GppConformalShadow

/-- The dilation `(D_a f)(x) = √a f(a x)`. -/
noncomputable def dil (a : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ((Real.sqrt a : ℝ) : ℂ) * f (a * x)

/-- The shadow inversion `(J f)(x) = x⁻¹ f(x⁻¹)`. -/
noncomputable def shadow (f : ℝ → ℂ) (x : ℝ) : ℂ := ((x⁻¹ : ℝ) : ℂ) * f x⁻¹

/-- `J² = 1`. -/
theorem shadow_shadow (f : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) : shadow (shadow f) x = f x := by
  unfold shadow
  rw [inv_inv]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp

/-- `J D_a J = D_{1/a}`: the shadow inverts the dilation parameter. -/
theorem shadow_dil (f : ℝ → ℂ) {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    shadow (dil a (shadow f)) x = dil a⁻¹ f x := by
  unfold shadow dil
  beta_reduce
  have ha0 : a ≠ 0 := ha.ne'
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have e1 : (a * x⁻¹)⁻¹ = a⁻¹ * x := by field_simp
  rw [e1]
  have e2 : Real.sqrt a⁻¹ = (Real.sqrt a)⁻¹ := by rw [Real.sqrt_inv]
  rw [e2]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  have hs' : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hsq : ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) := by
    have := Real.mul_self_sqrt ha.le
    exact_mod_cast this
  push_cast
  field_simp
  rw [← hsq]
  ring

/-- Both `D_a` and `J` are isometries of `L²((0,∞))`: the shadow preserves the norm. -/
theorem integral_norm_sq_shadow (f : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), ‖shadow f x‖ ^ 2 = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => ‖f y‖ ^ 2) (p := -1) (by norm_num)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  simp only [shadow, norm_mul, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul, abs_neg, abs_one,
    one_mul, Real.rpow_neg_one]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx0.le, abs_of_pos (inv_pos.2 hx0)]
  have : (x : ℝ) ^ (2 : ℝ) = x ^ 2 := by norm_cast
  rw [this]
  field_simp

theorem integral_norm_sq_dil (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), ‖dil a f x‖ ^ 2 = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => ‖f y‖ ^ 2) 0 ha
  rw [mul_zero] at h
  have e : ∀ x : ℝ, ‖dil a f x‖ ^ 2 = a * ‖f (a * x)‖ ^ 2 := by
    intro x
    unfold dil
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt ha.le]
  simp_rw [e]
  rw [integral_const_mul, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- **The shadow transform in the Mellin picture.** `mellin (J f) s = mellin f (1 - s)`. -/
theorem mellin_shadow (f : ℝ → ℂ) (s : ℂ) : mellin (shadow f) s = mellin f (1 - s) := by
  have h1 : shadow f = fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) • (fun u : ℝ => f u⁻¹) t := by
    funext t
    unfold shadow
    rw [smul_eq_mul, cpow_neg_one]
    push_cast
    rfl
  rw [h1, mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

/-- **Primary states.** `x^{ρ-1}` is a dilation eigenstate: `D_a x^{ρ-1} = a^{ρ-1/2} x^{ρ-1}`. -/
theorem dil_cpow (ρ : ℂ) {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    dil a (fun y : ℝ => (y : ℂ) ^ (ρ - 1)) x = (a : ℂ) ^ (ρ - 1 / 2) * (x : ℂ) ^ (ρ - 1) := by
  unfold dil
  have hsq : ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    push_cast
    ring_nf
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hsq]
  push_cast
  rw [mul_cpow_ofReal_nonneg ha.le hx.le, ← mul_assoc, ← cpow_add _ _ ha0]
  congr 2
  ring

/-- **The shadow exchanges a state with its shadow state.** `J x^{ρ-1} = x^{(1-ρ)-1}`. -/
theorem shadow_cpow (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    shadow (fun y : ℝ => (y : ℂ) ^ (ρ - 1)) x = (x : ℂ) ^ ((1 - ρ) - 1) := by
  unfold shadow
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have h1 : (x : ℂ) * (x : ℂ) ^ (ρ - 1) = (x : ℂ) ^ ρ := by
    have := cpow_add (1 : ℂ) (ρ - 1) hx0
    rw [cpow_one, show (1 : ℂ) + (ρ - 1) = ρ by ring] at this
    exact this.symm
  push_cast
  rw [inv_cpow _ _ harg, show (1 - ρ - 1 : ℂ) = -ρ by ring, cpow_neg, ← h1, mul_inv]

/-- The shadow swaps `(0,1]` and `[1,∞)`: if `f` vanishes on `(1,∞)`, `J f` vanishes on `(0,1)`. -/
theorem shadow_eq_zero_of_lt_one {f : ℝ → ℂ} (hf : ∀ y, 1 < y → f y = 0) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) : shadow f x = 0 := by
  unfold shadow
  rw [hf x⁻¹ (one_lt_inv_iff₀.2 ⟨hx0, hx1⟩), mul_zero]

/-- **`J` maps `L²(0,1]` isometrically onto `L²[1,∞)`.** If `f` vanishes on `(1,∞)` and is square
integrable, the shadow carries all of its norm to `(1,∞)`. -/
theorem integral_norm_sq_shadow_Ioi {f : ℝ → ℂ} (hf : ∀ y, 1 < y → f y = 0)
    (hint : IntegrableOn (fun x => ‖shadow f x‖ ^ 2) (Ioi (0 : ℝ))) :
    ∫ x in Ioi (1 : ℝ), ‖shadow f x‖ ^ 2 = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  rw [← integral_norm_sq_shadow f]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hI1 : ∫ x in Ioc (0 : ℝ) 1, ‖shadow f x‖ ^ 2 = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
    rw [shadow_eq_zero_of_lt_one hf hx.1 hx.2]
    simp
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (by rw [hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [hsplit]; exact subset_union_right)), hI1, zero_add]

/-- **The shadow of the Gaussian ground state.** On the strip, `mellin (J g) s = shadowCoeff s ·
mellin g s`. -/
theorem mellin_shadow_gaussian {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (shadow fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) s =
      GppArchimedeanCelestial.shadowCoeff s *
        mellin (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) s := by
  rw [mellin_shadow]
  have hr := GppArchimedeanCelestial.gaussian_shadow_ratio h0 h1
  have hne : mellin (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) s ≠ 0 := by
    rw [GppArchimedeanCelestial.mellin_gaussian h0]
    exact mul_ne_zero (by norm_num) (Gammaℝ_ne_zero_of_re_pos h0)
  rw [← hr]
  exact (div_mul_cancel₀ _ hne).symm

/-- **The shadow of the arithmetic profile.** For `χ(x) = {1/x}` and `0 < re s < 1`:
`(1 - s) · shadowCoeff s · mellin (J χ) s = s · mellin χ s`. -/
theorem shadow_arith_identity {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (1 - s) * GppArchimedeanCelestial.shadowCoeff s *
        mellin (shadow GppNymanBeurling.fracInv) s =
      s * mellin GppNymanBeurling.fracInv s := by
  rw [mellin_shadow, GppNymanBeurling.mellin_fracInv h0 h1,
    GppNymanBeurling.mellin_fracInv (by simp; linarith) (by simp; linarith)]
  have hs : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : 1 - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hz := GppArchimedeanCelestial.zeta_eq_shadowCoeff_mul h0 h1
  field_simp
  linear_combination hz

end GppConformalShadow

#print axioms GppConformalShadow.shadow_shadow
#print axioms GppConformalShadow.shadow_dil
#print axioms GppConformalShadow.integral_norm_sq_shadow
#print axioms GppConformalShadow.integral_norm_sq_dil
#print axioms GppConformalShadow.mellin_shadow
#print axioms GppConformalShadow.dil_cpow
#print axioms GppConformalShadow.shadow_cpow
#print axioms GppConformalShadow.integral_norm_sq_shadow_Ioi
#print axioms GppConformalShadow.mellin_shadow_gaussian
#print axioms GppConformalShadow.shadow_arith_identity
