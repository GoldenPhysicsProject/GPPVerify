import GppVerify.RiemannHypothesis.OneSidedPsiRH

/-!
# The Laplace transform of the prime signal `J₀`

Source: Astra, `work/2026-10-21_astra_joint_mobius_abel_obstruction.md` §1 (GPP-bridge), with
Codex's normalization `J₀(t) = ∫₀ᵗ e^{u/2} q(u) du`, `q(u) = e^{-u}ψ(eᵘ) − 1`
(`work/codex/2026-10-21_arithmetic_logblock_BV_ultraviolet_tail_alltime.md` §2). This is the same
signal as the `J(t)` of Daniel Toupin's prime-signal program. Daniel Toupin / Golden Physics
Project, with AI assistance from Astra (the identity) and Claude Code (formalization).

* `integral_f`: for `Re z > 1/2`, `∫₀^∞ e^{u/2}q(u) e^{-zu} du = L(Λ, z+½)/(z+½) − 1/(z−½)`. This
  uses `GppOneSidedRH.integral_psi_exp`, which rests on Mathlib's Abel-summation form of `L(Λ, ·)`.
* `integral_J0`: for `Re z > 1/2`, `∫₀^∞ J₀(t) e^{-zt} dt = (1/z) ∫₀^∞ e^{u/2}q(u) e^{-zu} du`,
  by Fubini on `{0 < u ≤ t}`, with absolute integrability from Chebyshev's bound.
* `laplace_J0_eq` (Astra's closed form): for `Re z > 1/2`,
  `∫₀^∞ J₀(t) e^{-zt} dt = −[ζ'/ζ(z+½) + 1/(z−½) + 1] / (z(z+½))`.

**Scope.** The identity is proved only for `Re z > 1/2`, where everything converges absolutely. The
note's continuation of the bounded-kernel transform to `Re z > 0`, the residue computation at zeros
with `Re ρ > 1/2`, and the Abel-energy pole bound (§2) are not formalized here. Nothing here
concerns where the zeros of `ζ` lie; RH is open.
-/

open MeasureTheory Set Complex Filter
open scoped ArithmeticFunction.vonMangoldt Chebyshev

namespace GppPrimeSignalLaplace

/-- The prime-signal derivative `f(u) = e^{u/2} (e^{-u} ψ(eᵘ) − 1)`. -/
noncomputable def f (u : ℝ) : ℝ := Real.exp (u / 2) * (Real.exp (-u) * ψ (Real.exp u) - 1)

/-- The prime signal `J₀(t) = ∫₀ᵗ e^{u/2}(e^{-u}ψ(eᵘ) − 1) du`. (The substitution `x = eᵘ` turns it
into `∫₁^{eᵗ} (ψ(x) − x) x^{-3/2} dx`; that rewriting is not formalized here.) -/
noncomputable def J0 (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, f u

lemma measurable_f : Measurable f :=
  (Real.measurable_exp.comp (measurable_id.div_const 2)).mul
    (((Real.measurable_exp.comp measurable_neg).mul
      ((Chebyshev.psi_mono.measurable).comp Real.measurable_exp)).sub measurable_const)

/-- `|f(u)| ≤ C e^{u/2}` with `C = log 4 + 5`. -/
lemma abs_f_le (u : ℝ) : |f u| ≤ (Real.log 4 + 5) * Real.exp (u / 2) := by
  have h1 := Chebyshev.psi_le_const_mul_self (Real.exp_pos u).le
  have h0 := Chebyshev.psi_nonneg (Real.exp u)
  have hq : |Real.exp (-u) * ψ (Real.exp u) - 1| ≤ Real.log 4 + 5 := by
    have hle : Real.exp (-u) * ψ (Real.exp u) ≤ Real.log 4 + 4 := by
      calc Real.exp (-u) * ψ (Real.exp u) ≤ Real.exp (-u) * ((Real.log 4 + 4) * Real.exp u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.log 4 + 4 := by rw [mul_left_comm, ← Real.exp_add]; simp
    have hge : 0 ≤ Real.exp (-u) * ψ (Real.exp u) := mul_nonneg (Real.exp_pos _).le h0
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    rw [abs_le]; constructor <;> linarith
  rw [f, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le

/-- **Laplace transform of the prime-signal derivative.** For `Re z > 1/2`,
`∫₀^∞ f(u) e^{-zu} du = L(Λ, z + 1/2)/(z + 1/2) − 1/(z − 1/2)`. -/
theorem integral_f {z : ℂ} (hz : 1 / 2 < z.re) :
    ∫ u in Ioi (0 : ℝ), (f u : ℂ) * Complex.exp (-z * u) =
      LSeries (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) / (z + 1 / 2) - 1 / (z - 1 / 2) := by
  have hz1 : 1 < (z + 1 / 2).re := by simp; linarith
  have hI1 := GppOneSidedRH.integrableOn_psi_kernel hz1
  have hI2 : IntegrableOn (fun u : ℝ => Complex.exp ((1 / 2 - z) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
  have hcongr : Set.EqOn (fun u : ℝ => (f u : ℂ) * Complex.exp (-z * u))
      (fun u : ℝ => (ψ (Real.exp u) : ℂ) * Complex.exp (-(z + 1 / 2) * u) -
        Complex.exp ((1 / 2 - z) * u)) (Ioi 0) := by
    intro u _
    simp only [f]
    push_cast
    have e1 : Complex.exp (-(z + 1 / 2) * u) =
        Complex.exp (u / 2) * Complex.exp (-u) * Complex.exp (-z * u) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    have e2 : Complex.exp ((1 / 2 - z) * u) = Complex.exp (u / 2) * Complex.exp (-z * u) := by
      rw [← Complex.exp_add]; ring_nf
    rw [e1, e2]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub hI1 hI2,
    GppOneSidedRH.integral_psi_exp hz1, integral_exp_mul_complex_Ioi (by simp; linarith)]
  have h1 : (1 / 2 : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2 : z - 1 / 2 ≠ 0 := fun h => h1 (by rw [← neg_sub, h, neg_zero])
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show -(1 : ℂ) / (1 / 2 - z) = 1 / (z - 1 / 2) by
    rw [show (1 : ℂ) / 2 - z = -(z - 1 / 2) by ring, div_neg, neg_div, neg_neg]]

/-- The Fubini kernel on `(u, t)`: `1[u ≤ t] f(u) e^{-zt}`. -/
noncomputable def kernel (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  if p.1 ≤ p.2 then (f p.1 : ℂ) * Complex.exp (-z * p.2) else 0

lemma norm_kernel (z : ℂ) (p : ℝ × ℝ) :
    ‖kernel z p‖ = if p.1 ≤ p.2 then |f p.1| * Real.exp (-z.re * p.2) else 0 := by
  unfold kernel
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]; simp
  · simp

lemma measurable_kernel (z : ℂ) : Measurable (kernel z) :=
  Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    ((Complex.measurable_ofReal.comp (measurable_f.comp measurable_fst)).mul
      (Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_snd)))) measurable_const

/-- The inner `t`-integral of `‖kernel‖`, for `u > 0`. -/
lemma integral_norm_kernel {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 < u) :
    ∫ t in Ioi (0 : ℝ), ‖kernel z (u, t)‖ = |f u| * (Real.exp (-z.re * u) / z.re) := by
  simp_rw [norm_kernel]
  have : (fun t : ℝ => if u ≤ t then |f u| * Real.exp (-z.re * t) else 0) =
      (Ici u).indicator (fun t => |f u| * Real.exp (-z.re * t)) := by
    ext t; simp [Set.indicator, Set.mem_Ici]
  rw [this, setIntegral_indicator measurableSet_Ici,
    show Ioi (0 : ℝ) ∩ Ici u = Ici u from inter_eq_right.mpr (Ici_subset_Ioi.mpr hu),
    integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  congr 1
  field_simp

lemma integrableOn_kernel_slice {z : ℂ} (hz : 0 < z.re) (u : ℝ) :
    Integrable (fun t => kernel z (u, t)) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -z.re < 0) 0).const_mul
    |f u|) ((measurable_kernel z).comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_kernel]
  split_ifs
  · exact le_rfl
  · positivity

lemma integrable_kernel {z : ℂ} (hz : 1 / 2 < z.re) :
    Integrable (kernel z) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hz0 : 0 < z.re := by linarith
  rw [integrable_prod_iff (measurable_kernel z).aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun u => integrableOn_kernel_slice hz0 u, ?_⟩
  have hbound : IntegrableOn (fun u : ℝ => (Real.log 4 + 5) / z.re *
      Real.exp ((1 / 2 - z.re) * u)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine Integrable.mono' hbound
    ((StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
      (measurable_kernel z).norm.stronglyMeasurable).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
    integral_norm_kernel hz0 hu]
  have hf := abs_f_le u
  have hx : Real.exp (u / 2) * Real.exp (-z.re * u) = Real.exp ((1 / 2 - z.re) * u) := by
    rw [← Real.exp_add]; ring_nf
  calc |f u| * (Real.exp (-z.re * u) / z.re)
      ≤ (Real.log 4 + 5) * Real.exp (u / 2) * (Real.exp (-z.re * u) / z.re) :=
        mul_le_mul_of_nonneg_right hf (by positivity)
    _ = (Real.log 4 + 5) / z.re * Real.exp ((1 / 2 - z.re) * u) := by
        rw [← hx]; field_simp

/-- **Laplace transform of the prime signal.** For `Re z > 1/2`,
`∫₀^∞ J₀(t) e^{-zt} dt = (1/z) ∫₀^∞ f(u) e^{-zu} du`. -/
theorem integral_J0 {z : ℂ} (hz : 1 / 2 < z.re) :
    ∫ t in Ioi (0 : ℝ), (J0 t : ℂ) * Complex.exp (-z * t) =
      (1 / z) * ∫ u in Ioi (0 : ℝ), (f u : ℂ) * Complex.exp (-z * u) := by
  have hz0 : 0 < z.re := by linarith
  have hzne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz0; linarith
  have hswap := integral_integral_swap (f := fun u t => kernel z (u, t))
    (integrable_kernel hz)
  -- inner integral over `u`, for fixed `t > 0`
  have hL : ∀ t ∈ Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), kernel z (u, t)) =
      (J0 t : ℂ) * Complex.exp (-z * t) := by
    intro t ht
    have : (fun u : ℝ => kernel z (u, t)) =
        (Iic t).indicator (fun u => (f u : ℂ) * Complex.exp (-z * t)) := by
      ext u; simp [kernel, Set.indicator, Set.mem_Iic]
    rw [this, setIntegral_indicator measurableSet_Iic, integral_mul_const, J0,
      intervalIntegral.integral_of_le (le_of_lt ht), ← integral_complex_ofReal,
      show Ioi (0 : ℝ) ∩ Iic t = Ioc 0 t from rfl]
  -- inner integral over `t`, for fixed `u > 0`
  have hR : ∀ u ∈ Ioi (0 : ℝ), (∫ t in Ioi (0 : ℝ), kernel z (u, t)) =
      (1 / z) * ((f u : ℂ) * Complex.exp (-z * u)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have : (fun t : ℝ => kernel z (u, t)) =
        (Ici u).indicator (fun t => (f u : ℂ) * Complex.exp (-z * t)) := by
      ext t; simp [kernel, Set.indicator, Set.mem_Ici]
    rw [this, setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici u = Ici u from inter_eq_right.mpr (Ici_subset_Ioi.mpr hu0),
      integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_exp_mul_complex_Ioi (by simp; linarith)]
    field_simp
  calc ∫ t in Ioi (0 : ℝ), (J0 t : ℂ) * Complex.exp (-z * t)
      = ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), kernel z (u, t) :=
        (setIntegral_congr_fun measurableSet_Ioi hL).symm
    _ = ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), kernel z (u, t) := hswap.symm
    _ = ∫ u in Ioi (0 : ℝ), (1 / z) * ((f u : ℂ) * Complex.exp (-z * u)) :=
        setIntegral_congr_fun measurableSet_Ioi hR
    _ = (1 / z) * ∫ u in Ioi (0 : ℝ), (f u : ℂ) * Complex.exp (-z * u) := integral_const_mul _ _

/-- **Astra's closed form** (2026-10-21): for `Re z > 1/2`,
`∫₀^∞ J₀(t) e^{-zt} dt = −[ζ'/ζ(z + 1/2) + 1/(z − 1/2) + 1] / (z (z + 1/2))`. -/
theorem laplace_J0_eq {z : ℂ} (hz : 1 / 2 < z.re) :
    ∫ t in Ioi (0 : ℝ), (J0 t : ℂ) * Complex.exp (-z * t) =
      -(deriv riemannZeta (z + 1 / 2) / riemannZeta (z + 1 / 2) + 1 / (z - 1 / 2) + 1) /
        (z * (z + 1 / 2)) := by
  have hz1 : 1 < (z + 1 / 2).re := by simp; linarith
  rw [integral_J0 hz, integral_f hz,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz1]
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; linarith
  have hzh : z + 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hzm : z - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [neg_div]
  generalize deriv riemannZeta (z + 1 / 2) / riemannZeta (z + 1 / 2) = x
  have h3 : (1 : ℂ) + z * 2 ≠ 0 := fun h => hzh (by linear_combination h / 2)
  have h4 : (-1 : ℂ) + z * 2 ≠ 0 := fun h => hzm (by linear_combination h / 2)
  field_simp
  ring_nf
  field_simp
  ring

end GppPrimeSignalLaplace
